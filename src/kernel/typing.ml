(** Main type-checking and subtyping functions. *)

open Extra
open Bindlib
open Sorts
open Pos
open Ast
open Epsilon
open Equiv
open Output
open Uvars
open Compare

type sorted = E : 'a sort * 'a ex loc -> sorted

(* Exceptions to be used in case of failure. *)
exception Type_error of sorted * prop * exn
let type_error : sorted -> prop -> exn -> 'a =
  fun t p e ->
    match e with
    | Type_error(E(_,t),_,_)
         when has_pos t.pos -> raise e
    | _                     -> raise (Type_error(t, p, e))

exception Subtype_msg of pos * string
let subtype_msg : pos -> string -> 'a =
  fun pos msg -> raise (Subtype_msg(pos, msg))

exception Subtype_error of term * prop * prop * exn
let subtype_error : term -> prop -> prop -> exn -> 'a =
  fun t a b e ->
    match e with
    | Subtype_error _   -> raise e
    | Failed_to_prove _ -> raise e
    | _                 -> raise (Subtype_error(t,a,b,e))

exception Cannot_unify of prop * prop
let cannot_unify : prop -> prop -> 'a =
  fun a b -> raise (Cannot_unify(a,b))

exception Loops of term
let loops : term -> 'a =
  fun t -> raise (Loops(t))

exception Reachable

exception No_typing_IH of strloc

exception No_subtyping_IH of strloc * strloc

exception Illegal_effect of Effect.effect

exception Unexpected_error of string
let unexpected : string -> 'a =
  fun msg -> raise (Unexpected_error(msg))

(* Log functions registration. *)
let log_sub = Log.register 's' (Some "sub") "subtyping informations"
let log_sub = Log.(log_sub.p)

let log_typ = Log.register 't' (Some "typ") "typing informations"
let log_typ = Log.(log_typ.p)

type auto_ctxt =
  { tlvl  : int
  ; clvl  : int
  ; doing : bool
  ; old   : blocked list
  ; todo  : (int * blocked) list
  ; auto  : bool }

(* constant for loop detection in sub typing *)
let sub_max = ref 10

let default_auto_lvl = ref (0, 1)

let auto_empty () =
  { tlvl  = snd !default_auto_lvl
  ; clvl  = fst !default_auto_lvl
  ; doing = false
  ; old   = []
  ; todo  = []
  ; auto  = true }

type sub_adone =
  SA : 'a sort * ('a, 'a) bndr * 'b sort * ('b,'b) bndr -> sub_adone

type lr = L | R
type path = Rc of string | Ap of lr | Ca of string | Cm | Df of string
type memo_info = Weak | Skip of int | NoInfo | OpDefi
type memo_tbl = { info  : memo_info ref
                ; below : memo_node ref }
and memo_node = MNil
              | MApp of memo_tbl * memo_tbl
              | MCas of memo_tbl * (string * memo_tbl) list
              | MRec of (string * memo_tbl) list

type memo_tmp = (memo_tbl * path list)

let empty_memo_tbl () = { info  = ref NoInfo
                        ; below = ref MNil }

let memo_move : memo_tmp -> path -> memo_tmp = fun (tbl,ps) p ->
  match !(tbl.below), p, ps with
  | MNil       , _   , _    -> (tbl, p::ps)
  | _          , _   , _::_ -> (tbl, p::ps)
  | MApp(t1,t2), Ap L, []   -> (t1, [])
  | MApp(t1,t2), Ap R, []   -> (t2, [])
  | MCas(m,ms) , Cm  , []   -> (m, [])
  | MCas(m,ms) , Ca n, []   -> (try (List.assoc n ms, [])
                                with Not_found -> (tbl, [p]))
  | MRec(ms)   , Rc n, []   -> (try (List.assoc n ms, [])
                                with Not_found -> (tbl, [p]))
  | _          , _   , _    -> assert false

let memo_create : memo_tbl -> path -> memo_tbl = fun tbl p ->
  let (tbl, ps) = memo_move (tbl,[]) p in
  if ps = [] then tbl else
    begin
      let nm = empty_memo_tbl in
      let open UTimed in
      (match !(tbl.below), p with
      | MNil      , Ap _ -> tbl.below := MApp(nm (), nm ())
      | MNil      , Cm   -> tbl.below := MCas(nm (), [])
      | MNil      , Ca n -> tbl.below := MCas(nm (), [n, nm ()])
      | MCas(m,ms), Ca n -> tbl.below := MCas(m, (n, nm ())::ms)
      | MNil      , Rc n -> tbl.below := MRec([n, nm ()])
      | MRec(ms)  , Rc n -> tbl.below := MRec((n, nm ())::ms)
      | _         , _    -> assert false);
      let (tbl, ps) = memo_move (tbl,[]) p in
      assert (ps = []);
      tbl
    end

let memo_find   : memo_tmp -> memo_info = fun (tbl, ps) ->
  if ps = [] then !(tbl.info) else NoInfo

let memo_insert : memo_tmp -> memo_info -> unit = fun (tbl, ps) info ->
  let tbl = List.fold_left memo_create tbl (List.rev ps) in
  let open UTimed in
  tbl.info := info

type memo     = (string * memo_tbl) list
type memo2    = memo * memo (*old memo/new memo*)

(* Context. *)
type ctxt  =
  { uvarcount : int ref
  ; equations : pool
  ; ctx_names : Bindlib.ctxt
  (* the first of the pair is positive, the second
     is stricly less than the first *)
  ; positives : (ordi * ordi) list
  ; fix_ihs   : ((t,v) bndr, fix_schema) Buckets.t
  ; sub_ihs   : sub_schema list
  ; sub_adone : (sub_adone * int) list
  ; top_ih    : Scp.index * ordi array
  ; add_calls : (unit -> unit) list ref
  ; auto      : auto_ctxt
  ; memo      : memo_tmp
  ; callgraph : Scp.t
  ; pretty    : Print.pretty list
  ; totality  : Effect.t }

let empty_ctxt ?(memo=empty_memo_tbl ()) () =
  { uvarcount = ref 0
  ; equations = empty_pool ()
  ; ctx_names = Bindlib.empty_ctxt
  ; positives = []
  ; fix_ihs   = Buckets.empty (==)
  ; sub_ihs   = []
  ; sub_adone = []
  ; top_ih    = (Scp.root, [| |])
  ; add_calls = ref []
  ; auto      = auto_empty ()
  ; callgraph = Scp.create ()
  ; pretty    = []
  ; memo      = (memo, [])
  (* Loop and CallCC not allowed at toplevel *)
  ; totality  = Effect.(known[]) }

let add_pretty ctx known p =
  if known then ctx else { ctx with pretty = p :: ctx.pretty }

let add_path x ctx =
  { ctx with memo = memo_move ctx.memo x }

let new_uvar : type a. ctxt -> a sort -> a ex loc = fun ctx s ->
  let c = ctx.uvarcount in
  let i = !c in incr c;
  log_uni "?%i : %a" i Print.sort s;
  Pos.none (UVar(s, { uvar_key = i
                    ; uvar_val = ref (Unset [])
                    ; uvar_pur = ref false}))

let opred ctx o =
  match (Norm.whnf o).elt with
  | Succ o' -> o'
  | _       -> new_uvar ctx O (* NOTE: Ordinal.less is always tested later *)

let add_positive : ctxt -> ordi -> ordi -> ctxt = fun ctx o oo ->
  let o = Norm.whnf o in
  match o.elt with
  | Conv    -> ctx
  | Succ(_) -> ctx
  | _       -> if List.exists (fun (o',_) -> eq_expr o o') ctx.positives then
                 ctx
               else
                 let ctx = add_pretty ctx false (Posi o) in
                 {ctx with positives = (o,oo) :: ctx.positives}

(* Instantation of heterogenous binder with uvars. *)
let rec instantiate : type a b. ctxt -> (a, b) bseq -> b =
  fun ctx seq ->
    match seq with
    | BLast(s,f) -> let u = new_uvar ctx s in
                    subst f u.elt
    | BMore(s,f) -> let u = new_uvar ctx s in
                    instantiate ctx (subst f u.elt)

let extract_vwit_type : valu -> prop = fun v ->
  match (Norm.whnf v).elt with
  | VWit{valu={contents = (_,a,_)}} -> a
  | VDef(v)                         -> v.value_type
  | _                  -> assert false (* should not happen *)

let extract_swit_type : stac -> prop = fun s ->
  match (Norm.whnf s).elt with
  | SWit{valu={contents=(_,a)}} -> a
  | _               -> assert false (* should not happen *)

type typ_rule =
  | Typ_VTyp   of sub_proof * typ_proof
  | Typ_TTyp   of sub_proof * typ_proof
  | Typ_TSuch  of typ_proof
  | Typ_VSuch  of typ_proof
  | Typ_VWit   of sub_proof
  | Typ_VDef   of value * sub_proof
  | Typ_DSum_i of sub_proof * typ_proof
  | Typ_DSum_e of typ_proof * typ_proof list
  | Typ_Func_i of sub_proof * typ_proof
  | Typ_Func_e of typ_proof * typ_proof
  | Typ_Func_s of typ_proof * typ_proof
  | Typ_Prod_i of sub_proof * typ_proof list
  | Typ_Prod_e of typ_proof
  | Typ_Name   of typ_proof * stk_proof
  | Typ_Mu     of typ_proof
  | Typ_Scis
  | Typ_FixY   of typ_proof
  | Typ_Ind    of fix_schema * sub_proof
  | Typ_Goal   of string
  | Typ_Prnt   of sub_proof
  | Typ_Repl   of typ_proof
  | Typ_Delm   of typ_proof
  | Typ_Cont
  | Typ_Clck   of sub_proof * typ_proof

and  stk_rule =
  | Stk_Push   of sub_rule * typ_proof * stk_proof
  | Stk_Fram   of typ_proof * stk_proof
  | Stk_SWit   of sub_rule
  | Stk_Goal   of string

and  sub_rule =
  | Sub_Equal
  | Sub_Func   of (sub_proof * sub_proof option) option
  | Sub_Prod   of sub_proof list
  | Sub_DSum   of sub_proof list
  | Sub_Univ_l of sub_proof
  | Sub_Exis_r of sub_proof
  | Sub_Univ_r of sub_proof
  | Sub_Exis_l of sub_proof
  | Sub_Rest_l of sub_proof option (* None means contradictory context. *)
  | Sub_Rest_r of sub_proof option
  | Sub_Impl_l of sub_proof option (* None means contradictory context. *)
  | Sub_Impl_r of sub_proof option
  | Sub_Memb_l of sub_proof option (* None means contradictory context. *)
  | Sub_Memb_r of sub_proof
  | Sub_Gene   of sub_proof
  | Sub_FixM_r of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixM_l of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_FixN_r of bool * sub_proof (* boolean true if infinite rule *)
  | Sub_Ind    of sub_schema
  | Sub_Scis

and typ_proof = term * prop * typ_rule
and stk_proof = stac * prop * stk_rule
and sub_proof = term * prop * prop * sub_rule

let learn_nobox : ctxt -> valu -> ctxt = fun ctx v ->
  let (known, equations) = add_nobox v ctx.equations in
  let ctx = add_pretty ctx known (Print.Rela (NoBox v)) in
  { ctx with equations }

let learn : ctxt -> rel -> ctxt = fun ctx c ->
  let (known, equations) = learn ctx.equations c in
  let ctx = add_pretty ctx known (Print.Rela c) in
  { ctx with equations }

let learn_value : ctxt -> term -> prop -> valu * ctxt = fun ctx t a ->
  let (v,ctx,nb) =
    match is_nobox_value t with
    | Some (v,nb) -> (v, ctx, nb)
    | None ->
       let ae =
         match (Norm.whnf a).elt with
         | Memb(u,_) when eq_expr t u -> a
         | _ -> Pos.none (Memb(t,a))
       in
       let (vwit, ctx_names) =
         vwit ctx.ctx_names idt_valu ae Ast.bottom
       in
       let ctx = { ctx with ctx_names } in
       let twit = Pos.none (Valu vwit) in
       let ctx = learn ctx (Equiv(t,true,twit)) in
       (vwit, ctx, false)
  in
  if nb then (v,ctx) else
    let ctx = learn_nobox ctx v in
    (v, ctx)

(* Safe version of Obj.repr *)
type any_bndr = Any : ('a,'b) bndr -> any_bndr [@@unboxed]

(* Add to the context some conditions.
   A condition c is added if c false implies wit in a is false.
   as wit may be assumed not box, if c false implies wit = Box,
   c can be added *)
let learn_equivalences : ctxt -> valu -> prop -> ctxt = fun ctx wit a ->
  let adone = ref [] in
  let rec fn ctx wit a =
    let twit = Pos.none (Valu wit) in
    match (Norm.whnf a).elt with
    | HDef(_,e)  -> fn ctx wit e.expr_def
    | Memb(t,a)  -> let ctx = learn ctx (Equiv(twit,true,t)) in
                    fn ctx wit a
    | Rest(a,c)  -> fn (learn ctx c) wit a
    | Exis(s, f) -> let (t, ctx_names) = ewit ctx.ctx_names s twit f in
                    let ctx = { ctx with ctx_names } in
                    fn ctx wit (bndr_subst f t.elt)
    | Prod(fs)   ->
       A.fold (fun lbl (_, b) ctx ->
           let (v,pool,ctx_names) =
             find_proj ctx.equations ctx.ctx_names wit lbl
           in
           let ctx = add_pretty ctx false (CPrj(wit,lbl,v)) in
           let ctx = { ctx with equations = pool; ctx_names } in
           fn ctx v b) fs ctx
    | DSum(fs)   ->
       begin
         match find_sum ctx.equations wit with
         | None ->
            if A.length fs = 1 then
              A.fold (fun c (_,b) ctx ->
                  let cwit = vdot wit c in
                  let (vwit, ctx) = learn_value ctx cwit b in
                  fn ctx vwit b) fs ctx
            else ctx
         | Some(s,v,pool) ->
            try
              let (_, b) = A.find s fs in
              let ctx = { ctx with equations = pool } in
              fn ctx v b
            with Not_found -> assert false (* NOTE check *)
       end
    (** Learn positivity of the ordinal *)
    | FixM(s,o,f,l)  ->
       if List.memq (Any f) !adone then ctx else
         begin
           adone := (Any f) :: !adone;
           let (bound, ctx) =
             match (Norm.whnf o).elt with
             | Succ(o) -> (o, ctx)
             | _       ->
                (** We know that o is positive and wit in a
                    so we can build an eps < o *)
                let f o = unroll_FixM s (Pos.none o) f l in
                let f = raw_binder "o" true 0 (mk_free O) f in
                let (o', ctx_names) = owmu ctx.ctx_names o twit (no_pos, f) in
                (o', { ctx with ctx_names })
           in
           let ctx = add_positive ctx o bound in
           fn ctx wit (unroll_FixM s bound f l)
         end
    | _          -> ctx
  in fn ctx wit a

let learn_equivalences_term : ctxt -> term -> prop -> ctxt = fun ctx t a ->
  match to_value t ctx.equations with
  | (Some(v), equations) ->
     let ctx = { ctx with equations } in
     learn_equivalences ctx v a
  | (_      , equations) ->
     { ctx with equations }

let rec is_singleton : prop -> term option = fun t ->
  match (Norm.whnf t).elt with
  | Memb(x,_) -> Some x
  | Rest(t,_) -> is_singleton t
  | _         -> None (* TODO #10: more cases are possible *)

(* add to the context some conditions.
   A condition c is added if c false implies wit in a is true.
   as wit may be assumed not box, if c false implies a = Top,
   c can be added

   The optional argument arg, is given when wit is a lambda.
   in this case, arg is a term such that (wit arg) not in c.
   Therefore, if c = Func(t in a,b) one must have arg t, otherwise
   arg could not be a counter example.
*)
let learn_neg_equivalences
    : ctxt -> valu -> valu option -> prop -> prop * ctxt =
  fun ctx wit arg a ->
    let adone = ref [] in
    let twit = Pos.none (Valu wit) in
    let rec fn ctx a =
      let a = Norm.whnf a in
      match (Norm.whnf a).elt, arg with
      | HDef(_,e), _ -> fn ctx e.expr_def
      | Impl(c,a), _ -> fn (learn ctx c) a
      | Univ(s,f), _ -> let (t, ctx_names) = uwit ctx.ctx_names s twit f in
                        let ctx = { ctx with ctx_names } in
                        let u = bndr_subst f t.elt in
                        fn ctx u
      | Func(t,b,_,_), Some arg -> (a, learn_equivalences ctx arg b)
      (** Learn positivity of the ordinal *)
      | FixN(s,o,f,l), _ ->
       if List.memq (Any f) !adone then (a, ctx) else
         begin
           adone := (Any f) :: !adone;
           let (bound, ctx) =
             match (Norm.whnf o).elt with
             | Succ(o) -> (o, ctx)
             | _       ->
                (** We know that o is positive and wit in a
                    so we can build an eps < o *)
                let f o = unroll_FixN s (Pos.none o) f l in
                let f = raw_binder "o" true 0 (mk_free O) f in
                let (o', ctx_names) = ownu ctx.ctx_names o twit (no_pos, f) in
                (o', { ctx with ctx_names })
           in
           let ctx = add_positive ctx o bound in
           fn ctx (unroll_FixN s bound f l)
         end
      | _          -> (a, ctx)
    in fn ctx a

let learn_neg_equivalences_term
    : ctxt -> term -> prop -> prop * ctxt =
  fun ctx t c ->
    (* term_is_value below cost too much if there is nothing to do *)
    let rec learn_has_job a =
      let a = Norm.whnf a in
      match a.elt with
      | HDef(_,e) -> learn_has_job e.expr_def
      | Impl(c,a) -> true
      | Univ(s,f) -> true
      | FixN(s,o,f,l) -> true
      | _ -> false
    in
    if learn_has_job c then
      match to_value t ctx.equations with
      | (None, equations)    -> (c, { ctx with equations })
      | (Some(v), equations) ->
         let ctx = { ctx with equations } in
         learn_neg_equivalences ctx v None c
    else (c, ctx)

let term_is_value : term -> ctxt -> bool * bool * ctxt = fun t ctx ->
  let (is_val, no_box, equations) = is_value t ctx.equations in
  (is_val, no_box, {ctx with equations})

let print_pos : out_channel -> (ordi * ordi) list -> unit =
  fun ch os ->
    match os with
    | [] -> output_string ch "∅"
    | os -> let print ch (o, oo) =
              Printf.fprintf ch "%a (> %a)" Print.ex o Print.ex oo
            in print_list print ", " ch os

let is_conv : ordi -> bool = fun o ->
  match (Norm.whnf o).elt with
  | Conv -> true
  | _    -> false

let type_chrono = Chrono.create "typing"
let sub_chrono = Chrono.create "subtyping"
let check_fix_chrono = Chrono.create "chkfix"
let check_sub_chrono = Chrono.create "chksub"

type check_sub =
  | Sub_Applies of sub_rule
  | Sub_New of ctxt * (prop * prop)

let rec subtype =
  let rec subtype : ctxt -> term -> prop -> prop -> sub_proof =
    fun ctx t a b ->
    log_sub "proving the subtyping judgment:";
    log_sub "  %a\n  ⊢ %a\n  ∈ %a\n  ⊆ %a"
      print_pos ctx.positives Print.ex t Print.ex a Print.ex b;
    let a = Norm.whnf a in
    let b = Norm.whnf b in
    log_sub "  %a\n  ⊢ %a\n  ∈ %a\n  ⊆ %a"
      print_pos ctx.positives Print.ex t Print.ex a Print.ex b;
    let (t_is_val, _, ctx) = term_is_value t ctx in
    (* heuristic to instanciate some unification variables *)
    let mu_nu_heuristique : type a. bool -> a sort -> o ex loc ->
                     (a, p) fix_args -> (a, a) bndr -> p ex loc -> unit
      = fun is_mu s1 o1 l1 f b ->
      let unif_ord o =
        match (Norm.whnf o).elt with
        | UVar(O,v) -> uvar_set v o1
        | _ -> ()
      in
      let rec unif_args
              : type a b c d. (a,b) fix_args -> (c,d) fix_args -> unit
      = fun l1 l2 ->
          match (l1, l2) with
          | (Ast.Cns(e1,l1), Ast.Cns(e2,l2)) ->
             let (s1, e1) = sort e1 in
             let (s2, e2) = sort e2 in
             begin
               match eq_sort s1 s2 with
               | Eq.Eq          -> ignore (unif_expr ctx.equations e1 e2);
                                   unif_args l1 l2
               | Eq.NEq ->
               match (eq_sort s1 V, eq_sort s2 T) with
               | (Eq.Eq, Eq.Eq) -> ignore (unif_expr ctx.equations
                                                     (Pos.none (Valu e1)) e2);
                                   unif_args l1 l2
               | _              ->
               match (eq_sort s1 T, eq_sort s2 V) with
               | (Eq.Eq, Eq.Eq) -> ignore (unif_expr ctx.equations
                                                     e1 (Pos.none (Valu e2)));
                                   unif_args l1 l2
               | _              -> ()
             end
          | _ -> ()
      in
      let do_fix
          : type b. b sort -> o ex loc -> (b,b) bndr -> (b,p) fix_args -> unit
        = fun s o g l2 ->
        unif_ord o;
        match eq_sort s s1 with
        | Eq.Eq  -> if unif_bndr ctx.equations s f g then unif_args l1 l2
        | Eq.NEq -> ()
      in
      let rec fn : p ex loc -> unit = fun b ->
        match ((Norm.whnf b).elt, is_mu) with
        | (HDef(s,d)     , _    ) -> fn d.expr_def
        | (Rest(b,_)     , _    ) -> fn b
        | (Impl(_,b)     , _    ) -> fn b
        | (FixM(s,o,g,l2), true ) -> do_fix s o g l2
        | (FixN(s,o,g,l2), false) -> do_fix s o g l2
        | _ -> ()
      in
      fn b
    in
    try let r =
      (* Same types.  *)
      if leq_expr ctx.equations ctx.positives a b then
        begin
          log_sub "reflexivity applies";
          Sub_Equal
        end
      else (
      log_sub "reflexivity does not applies";
      let ctx = check_adone ctx a b in
      match (a.elt, b.elt) with
      (* Unfolding of definitions. *)
      | (HDef(_,d)  , _          ) ->
          let (_, _, _, r) = subtype ctx t d.expr_def b in r
      | (_          , HDef(_,d)  ) ->
          let (_, _, _, r) = subtype ctx t a d.expr_def in r
      (* Universal quantification on the right. *)
      | (_          , Univ(s,f)  ) ->
         if t_is_val then
           let (eps, ctx_names) = uwit ctx.ctx_names s t f in
           let ctx = { ctx with ctx_names } in
           Sub_Univ_r(subtype ctx t a (bndr_subst f eps.elt))
         else
           gen_subtype ctx a b
      (* Existential quantification on the left. *)
      | (Exis(s,f)  , _          ) ->
         if t_is_val then
           let (eps, ctx_names) = ewit ctx.ctx_names s t f in
           let ctx = { ctx with ctx_names } in
           Sub_Exis_l(subtype ctx t (bndr_subst f eps.elt) b)
         else
           gen_subtype ctx a b
      (* Membership on the left. *)
      | (Memb(u,c)  , _          ) ->
         if t_is_val then
           try
             let ctx = learn ctx (Equiv(t,true,u)) in
             Sub_Memb_l(Some(subtype ctx t c b))
           with Contradiction -> Sub_Memb_l(None)
         (* NOTE may need a backtrack because a right rule could work *)
         else gen_subtype ctx a b
      (* Restriction on the left. *)
      | (Rest(c,e)  , _          ) ->
         if t_is_val then
           begin
             try  Sub_Rest_l(Some(subtype (learn ctx e) t c b))
             with Contradiction -> Sub_Rest_l(None)
           end
          (* NOTE may need a backtrack because a right rule could work *)
          else gen_subtype ctx a b
      (* Implication on the right. *)
      | (_          , Impl(e,c)  ) ->
         if t_is_val then
           begin
             try  Sub_Impl_r(Some(subtype (learn ctx e)t a c))
             with Contradiction -> Sub_Impl_r(None)
           end
          (* NOTE may need a backtrack because a right rule could work *)
          else gen_subtype ctx a b
      | (FixM(s,o,f,l), _          ) ->
          if t_is_val then (* avoid creating a witness with a unif var *)
            begin
              mu_nu_heuristique true s o l f b;
              let ctx, o' =
                let o = Norm.whnf o in
                match o.elt with
                  Succ o' -> (ctx, o')
                | _ ->
                   let f o = unroll_FixM s (Pos.none o) f l in
                   let f = raw_binder "o" true 0 (mk_free O) f in
                   let (o', ctx_names) = owmu ctx.ctx_names o t (no_pos,f) in
                   let ctx = { ctx with ctx_names } in
                   (add_positive ctx o o', o')
              in
              Sub_FixM_l(false, subtype ctx t (unroll_FixM s o' f l) b)
            end
          else gen_subtype ctx a b
      | (_          , FixN(s,o,f,l)) ->
         if t_is_val then (* avoid creating a witness with a unif var *)
           begin
             mu_nu_heuristique false s o l f a;
             let ctx, o' =
               let o = Norm.whnf o in
               match o.elt with
                 Succ o' -> (ctx, o')
               | _ ->
                  let f o = unroll_FixN s (Pos.none o) f l in
                  let f = raw_binder "o" true 0 (mk_free O) f in
               let (o', ctx_names) = ownu ctx.ctx_names o t (no_pos, f) in
               let ctx = { ctx with ctx_names } in
               (add_positive ctx o o', o')
             in
             Sub_FixN_r(false, subtype ctx t a (unroll_FixN s o' f l))
            end
          else gen_subtype ctx a b
      | _ ->
      match Chrono.add_time check_sub_chrono (check_sub ctx a) b with
      | Sub_Applies prf    -> prf
      | Sub_New(ctx,(a,b)) ->
      match (a.elt, b.elt) with
      (* Arrow types. *)
      | (Func(t1,a1,b1,l1), Func(t2,a2,b2,l2)) when t_is_val ->
         (* check that totality and lazy agree *)
         log_sub "effect test";
         if not (Effect.sub t1 t2) then subtype_msg a.pos "Arrow clash";
         if l2 = Lazy && l1 = NoLz then subtype_msg a.pos "Lazy clash";
         log_sub "effect agree";
         (* build the nobox value witness *)
         begin try
         let w =
           let x = new_var (mk_free V) (Print.get_lambda_name t) in
           unbox (bind_var x (appl no_pos l1 (box t) (valu no_pos (vari no_pos x))))
         in
         (* NOTE : if the "let in" below raise Contradiction, this means that
                   a2 is empty, a2 => b2 is then at least all function and no
                   need to check b1 < b2 *)
         let (wit, ctx) =
           match is_singleton a2 with
           | Some(wit) ->
              let (_,ctx) = learn_value ctx wit a2 in
              (wit, ctx)
           | _ ->
              let (vwit, ctx_names) = vwit ctx.ctx_names (no_pos, w) a2 b2 in
              let ctx = { ctx with ctx_names } in
              let ctx = learn_nobox ctx vwit in
              let wit = Pos.none (Valu(vwit)) in
              (* learn the equation from a2. *)
              let ctx = learn_equivalences ctx vwit a2 in
              (wit, ctx)
         in
         (* the local term for b1 < b2 *)
         let rwit = Pos.none (Appl(t, wit, l1)) in
         (* if the first function type is total, we can assume that
            the above witness is a value.
            NOTE: we can not build ctx_f now, because we need to use
            ctx first below and it would trigger reset of the pool *)
         let check_right () =
           try
             let (rwit,ctx_f) =
               if Effect.(know_sub t1 []) then
                 let (v,ctx) = learn_value ctx rwit top in
                 (Pos.none (Valu v), ctx)
               else (rwit, ctx)
             in
             Some(subtype ctx_f rwit b1 b2)
           with
             Contradiction -> None
         in
         let is_uvar a = match (Norm.whnf a).elt
           with UVar _ -> true | _ -> false
         in
         let p1, p2 =
           (* heuristic to choose what to check first *)
           match is_singleton a1, is_singleton a2 with
           | Some _, _ | _, Some _
                when not (is_uvar a1) && not (is_uvar a2) ->
              let p1 = subtype ctx wit a2 a1 in
              let p2 = check_right () in
              (p1,p2)
           | _     , _ ->
              let p2 = check_right () in
              let p1 = subtype ctx wit a2 a1 in
              (p1,p2)
         in
         Sub_Func(Some(p1,p2))
         with Contradiction -> Sub_Func(None)
         end
      (* Product (record) types. *)
      | (Prod(fs1)  , Prod(fs2)  ) when t_is_val ->
          let check_field l (_,p,a2) ps =
            let a1 =
              try snd (A.find l fs1) with Not_found ->
              subtype_msg p ("Product clash on label " ^ l ^ "...")
            in
            let t = unbox (t_proj no_pos (box t) [no_pos, Pos.none l]) in
            let p = subtype ctx t a1 a2 in
            p::ps
          in
          (** NOTE: subtype fields with unification variables not under
              fixpoint first to allow for inductive proof *)
          let count l a2 =
            nb_vis_uvars a2
            + (try nb_vis_uvars (snd (A.find l fs1)) with Not_found -> 0)
          in
          let fs2 = A.mapi (fun l (p,a2) -> (count l a2, p, a2)) fs2 in
          let fs2 = A.sort (fun (n,_,_) (m,_,_) -> m - n) fs2 in
          let ps = A.fold check_field fs2 [] in
          Sub_Prod(ps)
      (* Disjoint sum types. *)
      | (DSum(cs1)  , DSum(cs2)  ) when t_is_val ->
          (* NOTE: then next line can not raise contradiction, t_is_val !*)
          let (wit, ctx) = try learn_value ctx t a
                           with Contradiction -> assert false
          in
          let check_variant c (_,p,a1) ps =
            try
              let cwit = vdot wit c in
              let (vwit, ctx) = learn_value ctx cwit a1 in
              let ctx =
                let t1 = Pos.none (Valu(Pos.none (Cons(Pos.none c, vwit)))) in
                learn ctx (Equiv(t1,true,t))
              in
              let a2 =
                try snd (A.find c cs2) with Not_found ->
                  subtype_msg p ("Sum clash on constructor " ^ c ^ "...")
              in
              let p = subtype ctx (Pos.none (Valu vwit)) a1 a2 in
              p::ps
            with Contradiction -> (t,a1,a1,Sub_Scis)::ps
          in
          (** NOTE: subtype fields with unification variables not under
              fixpoint first to allow for inductive proof *)
          let count c a1 =
            nb_vis_uvars a1
            + (try nb_vis_uvars (snd (A.find c cs2)) with Not_found -> 0)
          in
          let cs1 = A.mapi (fun c (p,a1) -> (count c a1, p, a1)) cs1 in
          let cs1 = A.sort (fun (n,_,_) (m,_,_) -> m - n) cs1 in
          let ps = A.fold check_variant cs1 [] in
          Sub_DSum(ps)
      (* Universal quantification on the left. *)
      | (Univ(s,f)  , _          ) ->
          if t_is_val then (* avoid creating a witness with a unif var *)
            let u = new_uvar ctx s in
            Sub_Univ_l(subtype ctx t (bndr_subst f u.elt) b)
          else gen_subtype ctx a b
      (* Existential quantification on the right. *)
      | (_          , Exis(s,f)  ) ->
          if t_is_val then (* avoid creating a witness with a unif var *)
            let u = new_uvar ctx s in
            Sub_Exis_r(subtype ctx t a (bndr_subst f u.elt))
          else gen_subtype ctx a b
      (* Mu right and Nu Left, infinite case. *)
      | (_          , FixM(s,o,f,l)) when is_conv o ->
          Sub_FixM_r(true, subtype ctx t a (unroll_FixM s o f l))
      | (FixN(s,o,f,l), _          ) when is_conv o ->
          Sub_FixN_l(true, subtype ctx t (unroll_FixN s o f l) b)
      (* Mu right and Nu left rules, general case. *)
      | (_          , FixM(s,o,f,l)) ->
         let u = opred ctx o in
         let prf = subtype ctx t a (unroll_FixM s u f l) in
         if not (Ordinal.less_ordi ctx.positives u o) then
           subtype_msg b.pos "ordinal not suitable (μr rule)";
         Sub_FixM_r(false, prf)
      | (FixN(s,o,f,l), _          ) ->
         let u = opred ctx o in
         let prf = subtype ctx t (unroll_FixN s u f l) b in
         if not (Ordinal.less_ordi ctx.positives u o) then
           subtype_msg b.pos "ordinal not suitable (νl rule)";
         Sub_FixN_l(false, prf)
      (* Membership on the right. *)
      | (_          , Memb(u,b)  ) when t_is_val ->
          prove ctx.equations ctx.auto.old (Equiv(t,true,u));
          Sub_Memb_r(subtype ctx t a b)
      (* Restriction on the right. *)
      | (_          , Rest(c,e)  ) ->
         begin
           (* we learn the equation that we will prove below *)
           let prf =
             try  Some(subtype (learn ctx e) t a c)
             with Contradiction -> None
           in
           let ctx = learn_equivalences_term ctx t a in
           prove ctx.equations ctx.auto.old e;
           Sub_Rest_r(prf)
          end
      (* Implication on the left. *)
      | (Impl(e,c)   , _        ) ->
         begin
           (* we learn the equation that we will prove below *)
           let prf =
             try  Some(subtype (learn ctx e) t c b)
             with Contradiction -> None
           in
           prove ctx.equations ctx.auto.old e;
           Sub_Impl_l(prf)
          end
      (* Fallback to general witness. *)
      | (_          , _          ) when not t_is_val ->
         log_sub "general subtyping";
         gen_subtype ctx a b
      (* No rule apply. *)
      | _                          ->
         subtype_msg no_pos "No rule applies")
    in
    (t, a, b, r)
    with
    | Contradiction      -> assert false
    | Sys.Break as e     -> raise e
    | Out_of_memory as e -> raise e
    | e                  -> subtype_error t a b e
  in
  fun ctx t a b -> Chrono.add_time sub_chrono (subtype ctx t a) b

and auto_prove : ctxt -> exn -> term -> prop -> typ_proof  =
  fun ctx exn t ty ->
    log_aut "entering auto_prove (%a : %a)" Print.ex t Print.ex ty;
    (* Save utime to backtrack even on unification *)
    let st = UTimed.Time.save () in
    (* Tell we are in auto *)
    let first_auto = not ctx.auto.doing in
    let reraise e =
      raise (if first_auto then type_error (E(T,t)) ty e else e)
    in
    let ctx = { ctx with auto = { ctx.auto with doing = true } } in
    (* Get the blocked case/eval from the exception *)
    let bls =
      match exn with Failed_to_prove(_,bls) -> bls
                   | _ -> assert false
    in
    let old  = bls @ ctx.auto.old in
    let ctx = { ctx with auto = { ctx.auto with old }} in
    let bls = List.map (function
                  | BTot _ as b -> (ctx.auto.tlvl - 1, b)
                  | BCas _ as b -> (ctx.auto.clvl - 1, b)) bls
    in
    let bls = List.filter (fun (l, _) -> l >= 0) bls in
    let todo = bls @ ctx.auto.todo in
    let cmp b1 b2 = match (b1,b2) with
      | (_,BTot _), (_,BCas _) -> -1
      | (_,BCas _), (_,BTot _) ->  1
      | (n,BTot _), (m,BTot _) -> compare m n
      | (n,BCas _), (m,BCas _) -> compare m n
    in
    let todo = List.stable_sort cmp todo in
    let skip = match memo_find ctx.memo with
      | Skip n -> n
      | _      -> 0
    in
    let todo =
      let rec fn n l = match (n,l) with
        | (0, l) -> l
        | (n, []) -> assert false
        | (n, _::l) -> fn (n-1) l
      in
      fn skip todo
    in
    (* main recursive function trying all elements *)
    let rec fn nb ctx todo =
      UTimed.Time.rollback st;
      match todo with
      | [] -> reraise exn
      | (tlvl, BTot (_,e)) :: todo ->
         (* for a totality, we add a let to the term and typecheck *)
         let ctx = { ctx with auto = { ctx.auto with todo } } in
         (try
            let ctx = { ctx with auto = { ctx.auto with tlvl } } in
            (** we use the auto hint to disallow auto for the added totality *)
            let f = labs no_pos NoLz None (Pos.none "x")
                      (fun _ -> hint no_pos (Auto true) (box t))
            in
            let t = unbox (hint no_pos (Auto false)
                             (appl no_pos NoLz (valu no_pos f) (box e))) in
            log_aut "totality (%d,%d) [%d]: %a"
                    ctx.auto.clvl ctx.auto.tlvl (List.length todo) Print.ex e;
            let r = type_term ctx t ty in
            if nb > 0 then memo_insert ctx.memo (Skip nb);
            r
          with
          | Failed_to_prove _ as e -> reraise e
          | Sys.Break as e         -> raise e
          | Out_of_memory as e     -> raise e
          | Type_error _           -> fn (nb+1) ctx todo)
      | (clvl, BCas(_,e,cs)) :: todo ->
         (* for a blocked case analysis, we add a case! *)
         let ctx = { ctx with auto = { ctx.auto with todo } } in
         (try
            let ctx = { ctx with auto = { ctx.auto with clvl } } in
            (** we use the auto hint to disallow auto for the added case *)
            let mk_case c =
              A.add c (no_pos, Pos.none "x",
                       (fun _ -> hint no_pos (Auto true) (box t)))
            in
            let cases = List.fold_right mk_case cs A.empty in
            let t = match e.elt with
              Valu e -> case no_pos (box e) cases
              | _ ->
                 let f = labs no_pos NoLz None (Pos.none "x") (fun v ->
                             case no_pos (vari no_pos v) cases)
                 in
                 appl no_pos NoLz (valu no_pos f) (box e)
            in
            let t = unbox (hint no_pos (Auto false) t) in
            log_aut "cases    (%d,%d): %a" ctx.auto.clvl ctx.auto.tlvl Print.ex t;
            let r = type_term ctx t ty in
            if nb > 0 then memo_insert ctx.memo (Skip nb);
            r
          with
          | Failed_to_prove _ as e -> reraise e
          | Sys.Break as e         -> raise e
          | Out_of_memory as e     -> raise e
          | Type_error _           -> fn (nb+1) ctx todo)
    in fn skip ctx todo

and gen_subtype : ctxt -> prop -> prop -> sub_rule =
  fun ctx a b ->
    let (eps, ctx_names) = vwit ctx.ctx_names idt_valu a b in
    let ctx = { ctx with ctx_names } in
    let ctx = learn_nobox ctx eps in
    let wit = Pos.none (Valu eps) in
    Sub_Gene(subtype ctx wit a b)

and check_adone : ctxt -> prop -> prop -> ctxt = fun ctx a b ->
  let gn (SA(s1,f1,s2,f2) as sa) =
    let eq (SA(t1,g1,t2,g2),n) =
      match (eq_sort s1 t1, eq_sort s2 t2) with
      | (Eq.Eq, Eq.Eq) -> f1 == g1 && f2 == g2
      | (_    , _    ) -> false
    in
    let n = try snd (List.find eq ctx.sub_adone) with Not_found -> 0 in
    if n >= !sub_max then
      begin
        log_sub "loop detected";
        raise (No_subtyping_IH (bndr_name f1, bndr_name f2))
      end;
    { ctx with sub_adone = (sa, n+1) :: ctx.sub_adone }
  in
  let rec fn a b =
    match ((Norm.whnf a).elt, (Norm.whnf b).elt) with
    | (HDef(_,d)      , _              ) -> fn d.expr_def b
    | (_              , HDef(_,d)      ) -> fn a d.expr_def
    | (FixM(s1,_,f1,_), FixM(s2,_,f2,_)) -> gn (SA(s1,f1,s2,f2))
    | (FixM(s1,_,f1,_), FixN(s2,_,f2,_)) -> gn (SA(s1,f1,s2,f2))
    | (FixN(s1,_,f1,_), FixM(s2,_,f2,_)) -> gn (SA(s1,f1,s2,f2))
    | (FixN(s1,_,f1,_), FixN(s2,_,f2,_)) -> gn (SA(s1,f1,s2,f2))
    | (_              , _              ) -> ctx
  in
  fn a b

and check_sub : ctxt -> prop -> prop -> check_sub = fun ctx a b ->
  (* Looking for potential induction hypotheses. *)
  let ihs = ctx.sub_ihs in
  log_sub "there are %i potential subtyping induction hypotheses"
    (List.length ihs);
  (* Function for finding a suitable induction hypothesis. *)
  let rec find_suitable ihs =
    match ihs with
    | ih::ihs ->
        begin
          try
            (* Elimination of the schema, and unification with goal type. *)
            let spe = elim_sub_schema ctx ih in
            let (a0, b0) = spe.sspe_judge in
            (* Check if schema applies. *)
            if not (UTimed.pure_test
                      (fun () -> leq_expr ctx.equations ctx.positives b0 b &&
                                 leq_expr ctx.equations ctx.positives a a0)
                      ())
            then raise Exit;
            (* Check positivity of ordinals. *)
            let ok =
              let fn (o,_) = Ordinal.is_pos ctx.positives o in
              let gn (o1,o2) = Ordinal.less_ordi ctx.positives o2 o1 in
              List.for_all fn spe.sspe_relat && List.for_all gn spe.sspe_relat
            in
            if not ok then raise Exit;
            (* Add call to call-graph and build the proof. *)
            add_call ctx (ih.ssch_index, spe.sspe_param) true;
            Sub_Applies(Sub_Ind(ih))
          with Exit -> find_suitable ihs
        end
    | []      ->
        (* No matching induction hypothesis. *)
        let no_uvars () =
          uvars ~ignore_epsilon:true a = [] &&
          uvars ~ignore_epsilon:true b = []
        in
        log_sub "no suitable induction hypothesis";
        match a.elt, b.elt with
        (* TODO #5 to avoid the restiction no_uvars () below,
           subml introduces unification variables parametrised by the
           generalised ordinals *)
        | (FixN _, _     )
        | (_     , FixM _)
        | (DSum _, DSum _)
        | (Prod _, Prod _) when no_uvars () ->
           (* Construction of a new schema. *)
           let (sch, os) = sub_generalise ctx a b in
           (* Registration of the new top induction hypothesis and call. *)
           add_call ctx (sch.ssch_index, os) false;
           (* Recording of the new induction hypothesis. *)
           log_sub "the schema has %i arguments" (Array.length os);
           let ctx = { ctx with sub_ihs = sch :: ctx.sub_ihs } in
           (* Instantiation of the schema. *)
           let (spe, ctx) = inst_sub_schema ctx sch os in
           let ctx = {ctx with positives = spe.sspe_relat} in
           Sub_New({ctx with top_ih = (sch.ssch_index, spe.sspe_param)},
                   spe.sspe_judge)
        | _ ->
           Sub_New(ctx, (a, b))

  in find_suitable ihs

and has_loop : prop -> bool =
  fun c ->
    let rec fn a =
      let a = Norm.whnf a in
      match a.elt with
      | HDef(_,e) -> fn e.expr_def
      | Impl(c,a) -> fn a
      | Rest(a,c) -> fn a
      | Univ(s,f) -> let t = bndr_term f in fn t
      | Exis(s,f) -> let t = bndr_term f in fn t
      | Memb(_,a) -> fn a
      | Func(t,_,a,_) -> Effect.(know_present Loop t) || fn a
      | _         -> false
    in fn c

and check_fix
    : ctxt -> term -> (t, v) bndr -> prop -> unit -> typ_proof =
  fun ctx t b c ->
  (* Looking for potential induction hypotheses. *)
  let ihs = Buckets.find b ctx.fix_ihs in
  log_typ "there are %i potential fixpoint induction hypotheses"
    (List.length ihs);
  (* Function for finding a suitable induction hypothesis. *)
  let rec find_suitable ihs =
    match ihs with
    | ih::ihs ->
       begin
         try
           (* An induction hypothesis has been found. *)
           let spe = elim_fix_schema ctx ih in
           log_typ "an induction hypothesis has been found, trying";
           log_typ "   %a\n < %a" Print.ex (snd spe.fspe_judge) Print.ex c;
           let prf =
             Chrono.add_time type_chrono
               (subtype ctx t (snd spe.fspe_judge)) c
           in
           log_typ "it matches\n%!";
           (* Do we need to check for termination *)
           let safe =
             ih.fsch_safe || not Effect.(present Loop ctx.totality)
           in
           (* Add call to call-graph and build the proof. *)
           if safe then
             add_call ctx (ih.fsch_index, spe.fspe_param) true;
           (t, c, Typ_Ind(ih,prf))
         with Subtype_error _ | Exit -> find_suitable ihs
       end
    | []      ->
       (* No matching induction hypothesis. *)
       log_typ "no suitable induction hypothesis";
       type_error (E(T,t)) c (No_typing_IH(bndr_name b))
  in
  if ihs = [] then
    begin
      (* Construction of a new schema. *)
      (* Do we need to check for termination *)
      let safe = not (has_loop c) in
      let (sch, os) = fix_generalise safe ctx b c in
      (* Registration of the new top induction hypothesis and call. *)
      add_call ctx (sch.fsch_index, os) false;
      (* Recording of the new induction hypothesis. *)
      log_typ "the schema has %i arguments" (Array.length os);
      let ctx = { ctx with fix_ihs = Buckets.add b sch ctx.fix_ihs } in
      (* Instantiation of the schema. *)
      let (spe, ctx) = inst_fix_schema ctx sch os in
      let ctx = {ctx with top_ih = (sch.fsch_index, spe.fspe_param)} in
      (* Unrolling of the fixpoint and proof continued. *)
      let v = bndr_subst b t.elt in
      (fun () ->
        Chrono.add_time type_chrono (type_valu ctx v) (snd spe.fspe_judge))
    end
  else
    let res = find_suitable ihs in (fun () -> res)

(** function building the relations between ordinals *)
and get_relat  : ordi array -> (int * int) list =
  fun os ->
    let l = ref [] in
    Array.iteri (fun i o ->
      let rec gn o = match (Norm.whnf o).elt with
        | OWMu{valu={contents = (o',_,_)}}
        | OWNu{valu={contents = (o',_,_)}}
        | OSch(_,Some o',_)
        | Succ(o') ->
           (try hn (Array.length os - 1) o' with Not_found -> gn o')
        | _ -> ()
      and hn j o' =
        if eq_expr o' os.(j) then l:= (j,i)::!l
        else if j > 0 then hn (j-1) o' else raise Not_found
      in
      gn o
      ) os;
    !l

(* Generalisation (construction of a fix_schema). *)
and sub_generalise : ctxt -> prop -> prop -> sub_schema * ordi array =
  fun ctx b c ->
    (* Extracting ordinal parameters from the goal type. *)
    let (ssch_judge, os) = Misc.bind2_ordinals ctx.equations b c in

    (* build the relations *)
    let ssch_relat = get_relat os in
    (* only keep the relations with a positive ordinals *)
    let is_posit (i,_) = Ordinal.is_pos ctx.positives os.(i) in
    let ssch_relat = List.filter is_posit ssch_relat in

    (* Build the judgment. *)
    (* Output.bug_msg "Schema: %a" Print.omb omb;*)

    (* Ask for a fresh symbol index. *)
    let ssch_index =
      let names = mbinder_names ssch_judge in
      Scp.create_symbol ctx.callgraph "$" names
    in
    (* Assemble the schema. *)
    ({ssch_index ; ssch_relat ; ssch_judge}, os)

(* Generalisation (construction of a fix_schema). *)
and fix_generalise
    : bool -> ctxt -> (t, v) bndr -> prop -> fix_schema * ordi array
  = fun safe ctx b c ->
    (* Extracting ordinal parameters from the goal type. *)
    let (omb, os) =
      if safe then Misc.bind_spos_ordinals c
      else Misc.fake_bind c
    in

    (* Build the judgment. *)
    (* Output.bug_msg "Schema: %a" Print.omb omb; *)
    let fsch_judge = (b, omb) in
    (* Ask for a fresh symbol index. *)
    let fsch_index =
      let name  = (bndr_name b).elt in
      let names = mbinder_names omb in
      Scp.create_symbol ctx.callgraph name names
    in
    (* Assemble the schema. *)
    ({fsch_index ; fsch_judge ; fsch_safe = safe }, os)

(* Elimination of a schema using ordinal unification variables. *)
and elim_fix_schema : ctxt -> fix_schema -> fix_specialised =
  fun ctx sch ->
    let arity = mbinder_arity (snd sch.fsch_judge) in
    let fspe_param = Array.init arity (fun _ -> new_uvar ctx O) in
    let xs = Array.map (fun e -> e.elt) fspe_param in
    let a = msubst (snd sch.fsch_judge) xs in
    let fspe_judge = (fst sch.fsch_judge, a) in
    { fspe_param ; fspe_judge }

(* Elimination of a schema using unification variables. *)
and elim_sub_schema : ctxt -> sub_schema -> sub_specialised =
  fun ctx sch ->
    let arity = mbinder_arity sch.ssch_judge in
    let sspe_param = Array.init arity (fun _ -> new_uvar ctx O) in
    let xs = Array.map (fun e -> e.elt) sspe_param in
    let rec fn = function
      | Cst(p1,p2) -> (p1,p2)
      | Bnd(s ,f ) -> fn (subst f (new_uvar ctx s).elt)
    in
    let sspe_judge = fn (msubst sch.ssch_judge xs) in
    let sspe_relat = List.map (fun (i,j) -> (sspe_param.(i),sspe_param.(j)))
                              sch.ssch_relat
    in
    { sspe_param ; sspe_relat; sspe_judge }

(* Instantiation of a schema with ordinal witnesses. *)
and inst_fix_schema : ctxt -> fix_schema -> ordi array
                      -> fix_specialised * ctxt =
  fun ctx sch os ->
    let arity = mbinder_arity (snd sch.fsch_judge) in
    let (eps, ctx_names) = cwit ctx.ctx_names (FixSch sch) in
    let ctx = { ctx with ctx_names } in
    let fn i = osch i None eps in
    let fspe_param = Array.init arity fn in
    let xs = Array.map (fun e -> e.elt) fspe_param in
    let a = msubst (snd sch.fsch_judge) xs in
    let fspe_judge = (fst sch.fsch_judge, a) in
    ({ fspe_param ; fspe_judge }, ctx)

(* Instantiation of a schema with ordinal witnesses. *)
and inst_sub_schema : ctxt -> sub_schema -> ordi array
                      -> sub_specialised * ctxt =
  fun ctx sch os ->
    let arity = mbinder_arity sch.ssch_judge in
    let (eps, ctx_names) = cwit ctx.ctx_names (SubSch sch) in
    let cache = ref [] in
    let rec fn i =
      try List.assoc i !cache with Not_found ->
        let bound = try Some (fn (List.assoc i sch.ssch_relat))
                    with Not_found -> None in
        let res = osch i bound eps in
        cache := (i,res)::!cache;
        res
    in
    let sspe_param = Array.init arity fn in
    let xs = Array.map (fun e -> e.elt) sspe_param in
    let rec fn i = function
      | Cst(p1,p2) -> (p1,p2)
      | Bnd(s ,f ) -> fn (i+1) (subst f (esch s i eps).elt)
    in
    let sspe_judge = fn 0 (msubst sch.ssch_judge xs) in
    let sspe_relat = List.map (fun (i,j) -> (sspe_param.(i),sspe_param.(j)))
                              sch.ssch_relat
    in
    ({ sspe_param ; sspe_relat; sspe_judge }, ctx)

(* Add a call to the call-graph. *)
and add_call : ctxt -> (Scp.index * ordi array) -> bool -> unit =
  fun ctx callee is_rec ->
    let todo () =
      let caller = ctx.top_ih in
      let matrix = build_matrix ctx.callgraph ctx.positives callee caller in
      let callee = fst callee in
      let caller = fst caller in
      Scp.(add_call ctx.callgraph { callee ; caller ; matrix ; is_rec })
    in
    UTimed.(ctx.add_calls := todo :: !(ctx.add_calls))

(* Build a call-matrix given the caller and the callee. *)
and build_matrix : Scp.t -> (ordi * ordi) list ->
                     (Scp.index * ordi array) ->
                     (Scp.index * ordi array) ->
                     Scp.matrix = fun calls pos callee caller ->
  let open Scp in
  let w = Scp.arity (fst callee) calls in
  let h = Scp.arity (fst caller) calls in
  let tab = Array.init h (fun _ -> Array.make w Infi) in
  let square = fst callee = fst caller in

  let fn j oj i oi =
    assert(j < h); assert(i < w);
    let r =
      if Ordinal.less_ordi pos oi oj then Min1
      else if Ordinal.leq_ordi pos oi oj then Zero
      else Infi
    in
    tab.(j).(i) <- r
  in
  (** Heuristic: diagonal first, for better guess when unification
      variable remain.  Check: we can put a -1 in this case ?  *)
  if square then
    Array.iteri (fun j oj ->
        fn j oj j (snd callee).(j)) (snd caller);
  Array.iteri (fun j oj ->
      Array.iteri (fun i oi -> if not square || i != j then fn j oj i oi)
                  (snd callee)) (snd caller);
  { w ; h ; tab }

and type_valu : ctxt -> valu -> prop -> typ_proof = fun ctx v c ->
  let t = in_pos v.pos (Valu(v)) in
  log_typ "proving the value judgment:\n  %a\n  ⊢ %a\n  : %a"
    print_pos ctx.positives Print.ex v Print.ex c;
  try
  let r =
    match v.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
       let (_, _, r) = type_valu ctx (Norm.whnf v) c in r
    (* λ-abstraction. *)
    | LAbs(ao,f,l)  ->
       (* build the function type a => b with totality annotation
          tot as a fresh totality variable *)
       begin
         let a =
           match ao with
           | None   -> new_uvar ctx P
           | Some a -> a
         in
         let b = new_uvar ctx P in
           (* build the witness for typing *)
         let (wit,ctx_names) = vwit ctx.ctx_names f a b in
         try
           let tot = Effect.create () in
           if l = Lazy then ignore (Effect.absent CallCC tot);
           let ctx = { ctx with ctx_names; totality = tot } in
           (* learn equivalences both for subtyping below and typing *)
           let (c, ctx) = learn_neg_equivalences ctx v (Some wit) c in
           let c' = Pos.none (Func(tot,a,b,l)) in
           (* check subtyping *)
           let p1 = subtype ctx t c' c in
           (* learn now than witness exists *)
           let ctx = learn_nobox ctx wit in
           (* call typing *)
           let no_use = (bndr_name f).elt = "_" in
           let ctx = add_pretty ctx no_use (Decl(wit,a)) in
           let p2 = type_term ctx (bndr_subst f wit.elt) b in
           Typ_Func_i(p1,p2)
         with Contradiction ->
           warn_unreachable ctx (bndr_subst f wit.elt);
           Typ_Cont
       end
    (* Constructor. *)
    | Cons(d,w)   ->
       begin
         try
           let a = new_uvar ctx P in
           let c' = Pos.none (DSum(A.singleton d.elt (no_pos, a))) in
           let (c, ctx) = learn_neg_equivalences ctx v None c in
           let p1 = subtype ctx t c' c in
           let p2 = type_valu ctx w a in
           Typ_DSum_i(p1,p2)
         with Contradiction ->
           warn_unreachable ctx t;
           Typ_Cont
       end
    (* Record. *)
    | Reco(m)     ->
        let has_mem k =
          let rec fn u = match (Norm.whnf u).elt with
            | Exis(s,f) -> fn (bndr_term f)
            | Univ(s,f) -> fn (bndr_term f)
            | Memb(_,t) -> fn t
            | Rest(t,_) -> fn t
            | Impl(_,t) -> fn t
            | Prod(m)   ->
               begin
                 try
                   let (_,t) = A.find k m in
                   match (Norm.whnf t).elt with Memb _ -> true | _ -> false
                 with Not_found -> false
               end
            | _ -> false
          in
          fn c
        in
        let fn l t m =
          let ctx = add_path (Rc l) ctx in
          let a = new_uvar ctx P in
          let a = if has_mem l then
                    Pos.none (Memb(Pos.none (Valu (snd t)), a))
                  else a
          in
          A.add l (no_pos, box a) m
        in
        let pm = A.fold fn m A.empty in
        begin
          try
            let (c, ctx) = learn_neg_equivalences ctx v None c in
            let c' = unbox (strict_prod no_pos pm) in
            let p1 = subtype ctx t c' c in
            let p2s =
              let fn l (p, v) ps =
                log_typ "Checking field %s." l;
                let (_,a) = A.find l pm in
                let p = type_valu ctx v (unbox a) in
              p::ps
              in
              A.fold fn m []
            in
            Typ_Prod_i(p1,p2s)
          with Contradiction ->
            warn_unreachable ctx t;
            Typ_Cont
        end
    (* Scissors. *)
    | Scis        ->
       begin
         try
           let _ = learn_neg_equivalences ctx v None c in
           raise Reachable
         with Contradiction -> Typ_Cont
       end
    (* Coercion. *)
    | Coer(_,v,a) ->
       begin
         try
           let t = Pos.in_pos v.pos (Valu(v)) in
           let (c, ctx) = learn_neg_equivalences ctx v None c in
           let p1 = subtype ctx t a c in
           let p2 = type_valu ctx v a in
           Typ_VTyp(p1,p2)
         with Contradiction ->
           warn_unreachable ctx t;
           Typ_Cont
       end
    (* Such that. *)
    | Such(_,_,r) ->
       begin
         try
           let (a,v) = instantiate ctx r.binder in
           let (c,ctx) = learn_neg_equivalences ctx v None c in
           let (b,wopt,rev) =
             match r.opt_var with
             | SV_None    -> (c                  , Some(t), true)
             | SV_Valu(v) -> (extract_vwit_type v
                             , Some(Pos.none (Valu v)) , false)
             | SV_Stac(s) -> (extract_swit_type s, None, false)
           in
           let _ =
             try
               match (wopt, rev) with
               | (None  , false) -> ignore(gen_subtype ctx b a)
               | (Some t, false) -> ignore(subtype ctx t b a)
               | (Some t, true ) -> ignore(subtype ctx t a b)
               | _               -> assert false
             with Subtype_error _ -> cannot_unify b a
           in Typ_TSuch(type_valu ctx v c)
         with Contradiction ->
              warn_unreachable ctx t;
              Typ_Cont
       end
    (* Witness. *)
    | VWit(w)     ->
        let (_,a,_) = !(w.valu) in
        let p = subtype ctx t a c in
        Typ_VWit(p)
    (* Definition. *)
    | HDef(_,d)   ->
        let (_, _, r) = type_valu ctx d.expr_def c in r
    (* Value definition. *)
    | VDef(d)     ->
        begin
          let st = UTimed.Time.save () in
          try
            if memo_find ctx.memo = OpDefi then raise Exit;
            let p = subtype ctx t d.value_type c in
            Typ_VDef(d,p)
          with
            (* NOTE: some times, defined values like 0 :nat = Zero
               will fail for base case of sized function, this backtracking
               solves the problem and is not too expensive for value only.
               We do not do it for function *)
          | Sys.Break as e -> raise e
          | e -> match d.value_orig.elt with
                 | Valu { elt = LAbs _ } -> raise e
                 | Valu v when not (Timed.get ctx.equations.time d.value_clos) ->
                    begin
                      UTimed.Time.rollback st;
                      try
                        let ctx2 = add_path (Df d.value_name.elt) ctx in
                        let (_,_,r) = type_valu ctx2 v c in
                        memo_insert ctx.memo OpDefi;
                        r
                      with _ -> raise e
                    end
                 | _ -> raise e
        end
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal (value) %S %a" str print_wrn_pos v.pos;
        Print.pretty ctx.pretty;
        Printf.printf "|- %a\n%!" Print.ex c;
        Typ_Goal(str)
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_)     -> unexpected "∀-witness during typing..."
    | EWit(_)     -> unexpected "∃-witness during typing..."
    | ESch(_)     -> unexpected "schema-witness during typing..."
    | VPtr(_)     -> unexpected "VPtr during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
    | FixM(_)     -> invalid_arg "mu in terms forbidden"
    | FixN(_)     -> invalid_arg "nu in terms forbidden"
  in (Pos.in_pos v.pos (Valu(v)), c, r)
  with
  | Failed_to_prove _ as e -> raise e
  | Out_of_memory as e     -> raise e
  | Sys.Break as e         -> raise e
  | e                      -> type_error (E(V,v)) c e

and do_set_param ctx = function
  | Alvl(clvl,tlvl) ->
     let ctx = { ctx with auto = { ctx.auto with clvl; tlvl } } in
     (ctx, fun () -> ())
  | Logs(s)         ->
     let save = Log.get_enabled () in
     Log.set_enabled s;
     (ctx, fun () -> Log.set_enabled save)
  | Keep(b)         ->
     let save = !Equiv.keep_intermediate in
     Equiv.keep_intermediate := b;
     (ctx, fun () -> Equiv.keep_intermediate := save)

and is_typed : type a. a v_or_t -> a ex loc -> bool = fun t e ->
  let e = Norm.whnf e in
  match (t,e.elt) with
  | _, Coer(_,_,a)     -> true
  | _, VWit(w)         -> true
  | _, Appl(t,_,_)     -> is_typed VoT_T t
  | _, Valu(v)         -> is_typed VoT_V v
  | _, Proj(v,_)       -> is_typed VoT_V v
  | _, Cons(_,v)       -> is_typed VoT_V v
  | _, LAbs(_,b,_)     -> is_typed VoT_T (bndr_term b)
  | _, Reco(m)         -> A.for_all (fun _ v -> is_typed VoT_V (snd v)) m
  | _, VDef _          -> true
  | _, FixY _          -> true
  | _, Such(_,_,r)     -> let (a,u) = instantiate (empty_ctxt ()) r.binder in
                          is_typed t u
  | _, Hint(_,t)       -> is_typed VoT_T t
  | _                  -> false

and warn_unreachable ctx t =
  if not (is_scis t) && not ctx.auto.doing then
    begin
      if has_pos t.pos then
        Output.wrn_msg "unreachable code %a" Pos.print_wrn_pos t.pos
      else
        Output.wrn_msg "unreachable code..."

    end;

and type_term : ctxt -> term -> prop -> typ_proof = fun ctx t c ->
  log_typ "proving the term judgment:\n  %a\n  ⊢(%a) %a\n  : %a"
          print_pos ctx.positives Print.arrow ctx.totality
          Print.ex t Print.ex c;
  let st = UTimed.Time.save () in
  try
  let r =
    match t.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        let (_,_,r) = type_term ctx (Norm.whnf t) c in r
    (* Value. *)
    | Valu(v)     ->
        let (_, _, r) = type_valu ctx v c in r
    (* Application or strong application. *)
    | Appl(f,u,l) ->
       begin
         try
           let (c, ctx) = learn_neg_equivalences_term ctx t c in
           (* a fresh unif var for the type of u *)
           let a = new_uvar ctx P in
           let tot = ctx.totality in
           let rec check_f ctx strong a0 =
             let memo = ctx.memo in
             let old_decision = memo_find memo <> Weak in
             let ctx = add_path (Ap L) ctx in
             (* common code to check f *)
             if strong && old_decision then (* strong application *)
               let (a, strong) = (* do not add singleton if it is one *)
                 if is_singleton a <> None then (a0, false)
                 else (Pos.none (Memb(u,a0)), true)
               in
               let c = Pos.none (Func(tot,a,c,l)) in
               let st = UTimed.Time.save () in
               try
                 let (v,ctx) = learn_value ctx u a in
                 let ctx = learn_equivalences ctx v a in
                 type_term ctx f c
               with Contradiction      -> warn_unreachable ctx f;
                                          (t,c,Typ_Scis)
                  | Sys.Break as e     -> raise e
                  | Out_of_memory as e -> raise e
                  | _ when strong && is_typed VoT_T f ->
                     UTimed.Time.rollback st;
                     check_f ctx false a0
             else
               let r = type_term ctx f (Pos.none (Func(tot,a,c,l))) in
               memo_insert memo Weak;
               r
           in
           let (p1,p2,strong) =
             (* when u is not typed and f is, typecheck f first *)
             if is_typed VoT_T f && not (is_typed VoT_T u) then
               (* f will be of type ae => c, with ae = u∈a if we know the
               function will be total (otherwise it is illegal) *)
               let strong = Effect.(know_sub tot []) in
               (* type check f *)
               let p1 = check_f ctx strong a in
               (* check u *)
               let ctx = add_path (Ap R) ctx in
               let p2 = type_term ctx u a in
               (p1,p2,strong)
             else
               (* it we are not checking for a total application, we
               check with a fresh totality variable. Otherwise, the
               test is_tot bellow might force ctx.totality to Tot.
               tot1 < tot is checked at the end *)
               let ctx_u = if Effect.(know_sub tot []) then ctx else
                             { ctx with totality = Effect.create () } in
               let ctx_u = add_path (Ap R) ctx_u in
               let p2 = type_term ctx_u u a in
               (* If the typing of u was total,
               we can use strong application *)
               let strong = Effect.(absent CallCC ctx_u.totality) in
               if not Effect.(sub ctx_u.totality tot) then
                 subtype_msg f.pos "Arrow clash";
               (* type check f *)
               let p1 = check_f ctx strong a in
               (p1,p2,strong)
           in
           if strong then Typ_Func_s(p1,p2) else Typ_Func_e(p1,p2)
         with Contradiction ->
           warn_unreachable ctx t;
           Typ_Cont
       end
    (* Fixpoint *)
    | FixY(b)     ->
       let rec break_univ ctx c =
         match (Norm.whnf c).elt with
         | Univ(O,f) -> let (eps, ctx_names) = uwit ctx.ctx_names O t f in
                        let ctx = { ctx with ctx_names } in
                        break_univ ctx (bndr_subst f eps.elt)
         | _         -> (c, ctx)
       in
       let (c, ctx) = break_univ ctx c in
       let p =
         Chrono.add_time check_fix_chrono (check_fix ctx t b) c ()
       in
       Typ_FixY(p)
    (* μ-abstraction. *)
    | MAbs(b)     ->
       let (eps, ctx_names) = swit ctx.ctx_names b c in
       let ctx = { ctx with ctx_names } in
       let t = bndr_subst b eps.elt in
       let p = type_term ctx t c in
       Typ_Mu(p)
    (* Named term. *)
    | Name(pi,u)  ->
       if not Effect.(present CallCC ctx.totality) then
          type_error (E(T,t)) c (Illegal_effect CallCC);
        let a = new_uvar ctx P in
        (* type stack before seems better, generate subtyping
           constraints in the correct direction *)
        let p1 = type_stac ctx pi a in
        let p2 = type_term ctx u a in
        Typ_Name(p2,p1)
    (* Projection. *)
    | Proj(v,l)   ->
       let c = Pos.none (Prod(A.singleton l.elt (no_pos, c))) in
       Typ_Prod_e(type_valu ctx v c)
    (* Case analysis. *)
    | Case(v,m)   ->
       let a = new_uvar ctx P in
       let ctx_v = add_path Cm ctx in
       let p = type_valu ctx_v v a in (* infer a type to learn equivalences *)
       let fn d (p,_) m =
         let a = new_uvar ctx P in
         A.add d (p,a) m
       in
       let ts = A.fold fn m A.empty in
       let _p1 = subtype ctx (Pos.none (Valu v)) a (Pos.none (DSum(ts))) in
       let check d (p,f) ps =
         log_typ "Checking case %s." d;
         let (_,a) = A.find d ts in
         let vd = vdot v d in
         let a0 = Pos.none (Memb(vd, a)) in (* type for witness only *)
         let (wit, ctx_names) = vwit ctx.ctx_names f a0 c in
         let ctx = { ctx with ctx_names } in
         let ctx = add_path (Ca d) ctx in
         let t = bndr_subst f wit.elt in
         (try
            let ctx = learn_nobox ctx wit in
            let eq =
              let t1 = Pos.none (Valu(Pos.none (Cons(Pos.none d, wit)))) in
              let t2 = Pos.none (Valu(v)) in
              Equiv(t1,true,t2)
            in
            let ctx = learn ctx eq in
            let ctx = learn_equivalences ctx wit a in
            (fun () -> type_term ctx t c :: ps)
          with Contradiction ->
            warn_unreachable ctx t;
            (fun () -> (t,c,Typ_Scis)::ps)) ()
       in
       let ps = A.fold check m [] in
       Typ_DSum_e(p,List.rev ps)
    (* Coercion. *)
    | Coer(_,t,a)   ->
       begin
         try
           let (c, ctx) = learn_neg_equivalences_term ctx t c in
           let p1 = subtype ctx t a c in
           let p2 = type_term ctx t a in
           Typ_TTyp(p1,p2)
         with Contradiction ->
           warn_unreachable ctx t;
           Typ_Cont
       end
    (* Such that. *)
    | Such(_,_,r) ->
        let (a,t) = instantiate ctx r.binder in
        let (b,wopt,rev) =
          match r.opt_var with
          | SV_None   -> (c                  , Some(t)                , true )
          | SV_Valu v -> (extract_vwit_type v, Some(Pos.none (Valu v)), false)
          | SV_Stac s -> (extract_swit_type s, None                   , false)
        in
        let _ =
          try
            match wopt, rev with
            | None, _       -> ignore(gen_subtype ctx b a)
            | Some t, false -> ignore(subtype ctx t b a)
            | Some t, true  -> ignore(subtype ctx t a b)
          with Subtype_error _ -> cannot_unify b a
        in
        let p = type_term ctx t c in
        Typ_TSuch(p)
    (* Definition. *)
    | HDef(_,d)   ->
       let (_,_,r) = type_term ctx d.expr_def c in r
    (* Goal. *)
    | Goal(_,str) ->
        wrn_msg "goal (term) %S %a" str print_wrn_pos t.pos;
        Print.pretty ctx.pretty;
        Printf.printf "|- %a\n%!" Print.ex c;
        Typ_Goal(str)
    (* Printing. *)
    | Prnt(_)     ->
       let a = unbox (strict_prod no_pos A.empty) in
       let p = gen_subtype ctx a c in
       Typ_Prnt(t, a, c, p)
    (* Replacement. *)
    | Repl(t,u) ->
        let c = Pos.none (Memb(t,c)) in
        let p1 = type_term ctx u c in
        Typ_Repl(p1)
    | Delm(t)     ->
       let pure = Pure.pure c in
       let ctx =
         if pure then
           begin
             Effect.log_eff "pure";
             let tot1 = Effect.create () in
             assert (Effect.sub ~except:[CallCC] tot1 ctx.totality);
             if not (Effect.absent CallCC ctx.totality) then
               failwith "Useless delim";
             { ctx with totality = tot1 }
           end
         else failwith "Delim requires pure type"
       in
       let p = type_term ctx t c in
       Typ_Delm(p)
    | Clck(v) ->
       let a = new_uvar ctx P in
       let p = subtype ctx t (ac_right a v) c in
       let q = type_valu ctx v a in
       Typ_Clck(p,q)
    | Hint(h,t)   ->
       let ctx, restore =
         match h with
         | Eval ->
            (ctx, fun () -> ())
         | Sugar ->
            let ctx = { ctx with totality = Effect.bot } in
            let post () = ignore (subtype ctx t c (unbox unit_prod)) in
            (ctx, post)
         | Auto b ->
            ({ ctx with auto = { ctx.auto with auto = b }}, fun () -> ())
         | LSet(l) ->
            do_set_param ctx l
         | Close(b,vs) ->
            let st = ctx.equations.time in
            let time = List.fold_left (fun t v -> Timed.set t  v.value_clos b)
                         st vs;
            in
            let equations =
              if b then ctx.equations else reinsert_vdef vs ctx.equations
            in
            ({ ctx with equations = { equations with time } },
             fun () -> Timed.Time.rollback st);
       in
       (try
          let (_,_,r) = type_term ctx t c in
          restore (); r
        with e -> restore (); raise e)
    (* Constructors that cannot appear in user-defined terms. *)
    | UWit(_)     -> unexpected "∀-witness during typing..."
    | EWit(_)     -> unexpected "∃-witness during typing..."
    | ESch(_)     -> unexpected "schema-witness during typing..."
    | TPtr(_)     -> unexpected "TPtr during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | ITag(_)     -> unexpected "ITag during typing..."
    | FixM(_)     -> invalid_arg "mu in values forbidden"
    | FixN(_)     -> invalid_arg "nu in values forbidden"
  in (t, c, r)
  with
  | Contradiction      -> assert false
  | Failed_to_prove _ as e when ctx.auto.auto
                       -> UTimed.Time.rollback st; auto_prove ctx e t c
  | Sys.Break as e     -> raise e
  | Out_of_memory as e -> raise e
  | e                  -> type_error (E(T,t)) c e

and type_stac : ctxt -> stac -> prop -> stk_proof = fun ctx s c ->
  log_typ "proving the stack judgment:\n  %a\n  stk ⊢ %a\n  : %a"
    print_pos ctx.positives Print.ex s Print.ex c;
  try
  let r =
    match s.elt with
    (* Higher-order application. *)
    | HApp(_,_,_) ->
        let (_, _, r) = type_stac ctx (Norm.whnf s) c in r
    | SWit(w)   ->
        let (_,a) = !(w.valu) in
        Stk_SWit(gen_subtype ctx c a)
    (* Definition. *)
    | HDef(_,d)   ->
        let (_, _, r) = type_stac ctx d.expr_def c in r
    (* Goal *)
    | Goal(_,str) ->
        wrn_msg "goal (stack) %S %a" str print_wrn_pos s.pos;
        Print.pretty ctx.pretty;
        Printf.printf "|- %a\n%!" Print.ex c;
        Stk_Goal(str)
    (* Constructors that cannot appear in user-defined stacks. *)
    | Coer(_,_,_) -> .
    | Such(_,_,_) -> .
    | UWit(_)     -> unexpected "∀-witness during typing..."
    | EWit(_)     -> unexpected "∃-witness during typing..."
    | ESch(_)     -> unexpected "schema-witness during typing..."
    | UVar(_)     -> unexpected "unification variable during typing..."
    | Vari(_)     -> unexpected "Free variable during typing..."
    | ITag(_)     -> unexpected "Tag during typing..."
    | FixM(_)     -> invalid_arg "mu in stacks forbidden"
    | FixN(_)     -> invalid_arg "nu in stacks forbidden"
  in (s, c, r)
  with
  | Failed_to_prove _ as e -> raise e
  | Sys.Break as e         -> raise e
  | Out_of_memory as e     -> raise e
  | e                      -> type_error (E(S,s)) c e

exception Unif_variables

exception NoMemo

let get_memo name memo =
  let rec fn acc = function
      [] -> raise NoMemo
    | (name',tbl as c)::memo ->
       if name = name' then (tbl, List.rev_append acc memo)
       else fn (c::acc) memo
  in
  fn [] memo

let type_check : memo_tbl option -> term -> prop -> prop * typ_proof * memo_tbl =
  fun memo t a ->
  let st = Timed.Time.save () in
  try
    let ctx = empty_ctxt ?memo () in
    let prf = type_term ctx t a in
    List.iter (fun f -> f ()) (List.rev !(ctx.add_calls));
    if not (Scp.scp ctx.callgraph) then loops t;
    (* there is no way to parse unif variables in type,
       so [uvars a] hould be empty *)
    assert (uvars a = []);
    reset_tbls ();
    Timed.Time.rollback st;
    (Norm.whnf a, prf, fst ctx.memo)
  with e -> reset_tbls (); Timed.Time.rollback st; raise e

let type_check : string -> term -> prop -> memo2 -> prop * typ_proof * memo2 =
  fun name t a (o,n) ->
    try
      let (memo,o) = get_memo name o in
      let (p, prf, memo) = type_check (Some memo) t a in
      let n = (name,memo) :: n in
      (p, prf, (o,n))
    with
    | Out_of_memory | Sys.Break as e -> raise e
    | e ->
       let (p, prf, memo) = type_check None t a in
       let n = (name,memo) :: n in
       (p, prf, (o,n))

let type_check t = Chrono.add_time type_chrono (type_check t)

let is_subtype : prop -> prop -> bool = fun a b ->
  let st = Timed.Time.save () in
  try
    let ctx = empty_ctxt () in
    let _ = gen_subtype ctx a b in
    (* same as above *)
    assert(uvars a = [] && uvars b = []);
    List.iter (fun f -> f ()) (List.rev !(ctx.add_calls));
    let res = Scp.scp ctx.callgraph in
    reset_tbls ();
    Timed.Time.rollback st;
    res
  with _ ->
    reset_tbls (); Timed.Time.rollback st; false
