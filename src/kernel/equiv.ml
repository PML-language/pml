(** Equivalence decision procedure. During decision of equivalence, terms are
    stored in a graph (shared among all knonwn terms). Maximal sharing is
    attained by never inserting nodes that are already in the graph. Given
    such a graph (or pool), one will be able to read back the representative
    of a term by following the edges. *)

open Extra
open Bindlib
open Ptr
open Sorts
open Pos
open Ast
open Output
open Uvars
open Hash
open Compare
open Epsilon

let equiv_chrono = Chrono.create "equiv"
let pareq_chrono = Chrono.create "pareq"
let inser_chrono = Chrono.create "inser"

(* Log function registration. *)
let log_edp1 = Log.register 'e' (Some "equ") "equivalence decision procedure"
let log_edp2 = Log.register 'f' (Some "equ") "details of equivalence decision"
let log_edp1  = Log.(log_edp1.p)
let log_edp2 = Log.(log_edp2.p)
let log_aut = Log.register 'a' (Some "aut") "automatic proving informations"
let log_aut = Log.(log_aut.p)

(** Exception raise when the pool contains a contradiction. *)
exception Contradiction
let bottom () = raise Contradiction

(** Managment of closures, a closure is a binder with all closed subterms
    taken outside. They are necessary because expressions like add e1 e2 are
    reduced to a case analysis and e1 and e2 are then moved under a case. But
    one needs to know that e1 = f1 implies add e1 e2 = add f1 e2.  *)

(** funptr are normal closures used by bndr, it is a binder waiting for
    the arrays of values and terms that were taken outside to give back the
    initial binder *)
type ('a, 'b) funptr = (v ex, (t ex, ('a, 'b) bndr) mbinder) mbinder

(** funptr are then hashconsed *)
let hash_funptr : type a b.a sort -> (a, b) funptr -> int =
  fun s b ->
    let c = ref (-1) in
    let new_itag : type a. a sort -> a ex =
      fun s -> incr c; ITag(s,!c)
    in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag V) in
    let b = msubst b vs in
    let a = mbinder_arity b in
    let ts = Array.init a (fun _ -> new_itag T) in
    let b = msubst b ts in
    hash_bndr s b

let eq_funptr : type a b.a sort -> (a, b) funptr -> (a, b) funptr -> bool =
  fun s b1 b2 -> eq_mbinder (eq_mbinder (eq_bndr s)) b1 b2

type anyfunptr = T : 'a sort * 'b sort * ('a, 'b) funptr -> anyfunptr
module Fun =
  struct
    type t = anyfunptr

    let equal (T (sa1,sr1,f1)) (T (sa2,sr2,f2)) =
      match eq_sort sa1 sa2 with
      | Eq.Eq ->
         begin
           match eq_sort sr1 sr2 with
           | Eq.Eq -> eq_funptr sa1 f1 f2
           | _ -> false
         end
      | _ -> false

    let hash (T (sa,sr,f)) =
      Hashtbl.hash (hash_sort sa, hash_sort sr, hash_funptr sa f)
  end
module FunHash = Hashtbl.Make(Fun)

(** This is the main type of a binder closure *)
type ('a,'b) bndr_closure = ('a, 'b) funptr * VPtr.t array * Ptr.t array

(** this second type of closure is used for higher order term in the pool.
    It is rather similar to the previous one *)
type 'a clsptr = (v ex, (t ex, 'a ex loc) mbinder) mbinder

let hash_clsptr : type a. a clsptr -> int =
  fun b ->
    let c = ref (-1) in
    let new_itag : type a. a sort -> a ex =
      fun s -> incr c; ITag(s,!c)
    in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag V) in
    let b = msubst b vs in
    let a = mbinder_arity b in
    let vs = Array.init a (fun _ -> new_itag T) in
    let b = msubst b vs in
    hash_expr b

let eq_clsptr : type a. a clsptr -> a clsptr -> bool =
  fun b1 b2 -> eq_mbinder (eq_mbinder eq_expr) b1 b2

type anyclsptr = C : 'a sort * 'a clsptr -> anyclsptr
module Cls =
  struct
    type t = anyclsptr

    let equal (C (sa1,f1)) (C (sa2,f2)) =
      match eq_sort sa1 sa2 with
      | Eq.Eq -> eq_clsptr f1 f2
      | _ -> false

    let hash (C (sa,f)) =
      Hashtbl.hash (hash_sort sa, hash_clsptr f)
  end
module ClsHash = Hashtbl.Make(Cls)

type 'a closure = 'a clsptr * VPtr.t array * Ptr.t array

(** Closure substitution *)
let subst_closure (funptr,vs,ts) =
  let vs = Array.map (fun v -> VPtr v) vs in
  let ts = Array.map (fun t -> TPtr t) ts in
  msubst (msubst funptr vs) ts

(** Wrapper for higher-order application. *)
type _ ho_appl =
  | HO : 'a sort * ('a -> 'b) closure * 'a closure -> 'b ho_appl

(** Type of a value node. *)
type v_node =
  | VN_LAbs of (v, t) bndr_closure * laz
  | VN_Cons of A.key loc * VPtr.t
  | VN_Reco of VPtr.t A.t
  | VN_Defi of value   (* closed definition *)
  | VN_Scis
  | VN_VWit of (vwit, string) eps
  | VN_UWit of (v qwit, string) eps
  | VN_EWit of (v qwit, string) eps
  | VN_ESch of int * seps
  | VN_HApp of v ho_appl
  | VN_UVar of v uvar
  | VN_Vari of v var
  | VN_Goal of v ex loc

(** Type of a term node. *)
type t_node =
  | TN_Valu of VPtr.t
  | TN_Appl of Ptr.t * Ptr.t * laz
  | TN_MAbs of (s,t) bndr_closure
  | TN_Name of s ex loc * Ptr.t
  | TN_Proj of VPtr.t * A.key loc
  | TN_Case of VPtr.t * (v,t) bndr_closure A.t
  | TN_Delm of Ptr.t
  | TN_FixY of (t,v) bndr_closure * tn_fixy_state Timed.tref
  | TN_Prnt of string
  | TN_UWit of (t qwit, string) eps
  | TN_EWit of (t qwit, string) eps
  | TN_ESch of int * seps
  | TN_HApp of t ho_appl
  | TN_UVar of t uvar
  | TN_Vari of t var
  | TN_Goal of t ex loc

 and tn_fixy_state =
   | Prep
   | Init of Ptr.t

type _ ty += T_Node : t_node ty
           | V_Node : v_node ty

(** Printing closure. *)
let pcl : type a. out_channel -> a closure -> unit =
  fun ch (funptr,vs,ts) ->
    let prnt = Printf.fprintf in
    let pex = Print.ex in
    let (vvars,b) = unmbind funptr in
    let (tvars,t) = unmbind b in
    let vvars = if vs = [||] then [||] else vvars in
    let tvars = if ts = [||] then [||] else tvars in
    let fn ch =
      Array.iteri (fun i v ->
          let t = vs.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) VPtr.print t) vvars
    in
    let gn ch =
      Array.iteri (fun i v ->
          let t = ts.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) Ptr.print t) tvars
    in
    prnt ch "%a[%t][%t]" pex t fn gn

(** Printing function for value nodes. *)
let pbcl : type a b. a sort -> out_channel -> (a, b) bndr_closure -> unit =
  fun s ch (funptr,vs,ts) ->
    let prnt = Printf.fprintf in
    let pex = Print.ex in
    let (vvars,b) = unmbind funptr in
    let (tvars,b) = unmbind b in
    let (var,t)   = bndr_open b in
    let vvars = if vs = [||] then [||] else vvars in
    let tvars = if ts = [||] then [||] else tvars in
    let fn ch =
      Array.iteri (fun i v ->
          let t = vs.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) VPtr.print t) vvars
    in
    let gn ch =
      Array.iteri (fun i v ->
          let t = ts.(i) in
          let sep = if i = 0 then "" else ", " in
          prnt ch "%s%s<-%a" sep (name_of v) Ptr.print t) tvars
    in
    prnt ch "%s.%a[%t][%t]" (name_of var) pex t fn gn


let print_v_node : out_channel -> v_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | VN_LAbs(b,l)   -> prnt ch "VN_LAbs(%a,%b)" (pbcl V) b (l = Lazy)
  | VN_Cons(c,pv)  -> prnt ch "VN_Cons(%s,%a)" c.elt VPtr.print pv
  | VN_Reco(m)     -> let pelt ch (k, p) = prnt ch "%S=%a" k VPtr.print p in
                      prnt ch "VN_Reco(%a)" (Print.print_map pelt ":") m
  | VN_Defi(d)     -> prnt ch "VN_Defi(%s)" d.value_name.elt
  | VN_Scis        -> prnt ch "VN_Scis"
  | VN_VWit(w)     -> prnt ch "VN_VWit(%a)" pex (Pos.none (VWit(w)))
  | VN_UWit(w)     -> prnt ch "VN_UWit(%a)" pex (Pos.none (UWit(w)))
  | VN_EWit(w)     -> prnt ch "VN_EWit(%a)" pex (Pos.none (EWit(w)))
  | VN_ESch(i,w)   -> prnt ch "VN_ESch(%a)" pex (Pos.none (ESch(V,i,w)))
  | VN_HApp(e)     -> let HO(s,f,a) = e in
                      prnt ch "VN_HApp(%a,%a)" pcl f pcl a
  | VN_UVar(v)     -> prnt ch "VN_UVar(%a)" pex (Pos.none (UVar(V,v)))
  | VN_Vari(x)     -> prnt ch "VN_Vari(%s)" (name_of x)
  | VN_Goal(v)     -> prnt ch "VN_Goal(%a)" pex v
(** Printing function for term nodes. *)
let print_t_node : out_channel -> t_node -> unit = fun ch n ->
  let prnt = Printf.fprintf in
  let pex = Print.ex in
  match n with
  | TN_Valu(pv)    -> prnt ch "TN_Valu(%a)" VPtr.print pv
  | TN_Appl(pt,pu,l) ->
     prnt ch "TN_Appl(%a,%a,%b)" Ptr.print pt Ptr.print pu (l = Lazy)
  | TN_MAbs(b)     -> prnt ch "TN_MAbs(%a)" (pbcl S) b
  | TN_Name(s,pt)  -> prnt ch "TN_Name(%a,%a)" pex s Ptr.print pt
  | TN_Proj(pv,l)  -> prnt ch "TN_Proj(%a,%s)" VPtr.print pv  l.elt
  | TN_Case(pv,m)  -> let pelt ch (k, b) =
                        prnt ch "%S → %a" k (pbcl V) b
                      in
                      let pmap = Print.print_map pelt "|" in
                      prnt ch "TN_Case(%a|%a)" VPtr.print pv pmap m
  | TN_Delm(pt)    -> prnt ch "TN_Delm(%a)" Ptr.print pt
  | TN_FixY(b,_)   -> prnt ch "TN_FixY(%a)" (pbcl T) b
  | TN_Prnt(s)     -> prnt ch "TN_Prnt(%S)" s
  | TN_UWit(w)     -> prnt ch "TN_UWit(%a)" pex (Pos.none (UWit(w)))
  | TN_EWit(w)     -> prnt ch "TN_EWit(%a)" pex (Pos.none (EWit(w)))
  | TN_ESch(i,w)   -> prnt ch "TN_ESch(%a)" pex (Pos.none (ESch(V,i,w)))
  | TN_HApp(e)     -> let HO(s,f,a) = e in
                      prnt ch "TN_HApp(%a,%a)" pcl f pcl a
  | TN_UVar(v)     -> prnt ch "TN_UVar(%a)" pex (Pos.none (UVar(T,v)))
  | TN_Vari(x)     -> prnt ch "TN_Vari(%s)" (name_of x)
  | TN_Goal(t)     -> prnt ch "TN_Goal(%a)" pex t

(** Type of a pool. *)
type pool =
  { vs       : (VPtr.t * v_node) list
  ; ts       : (TPtr.t * t_node) list
  ; cvs      : (VPtr.t * v_node) list (* as above, but only node with no children *)
  ; cts      : (TPtr.t * t_node) list (* as above, but only node with no children *)
  ; os       : (Ptr.t * t ex loc) list
  ; next     : int    (** counter to generate new nodes *)
  ; time     : Timed.Time.t (** Current time for references *)
  ; ineq     : (ptr * ptr) list
  ; eq_map   : (ptr * ptr) list (* just for printing and debugging *)
  ; values   : (value * v_ptr) list
  ; v_defs   : (v expr * v_ptr) list
  ; e_defs   : (t expr * Ptr.t) list
  ; in_uni   : (Ptr.t * Ptr.t) list(* to avoid loop un unif_ptr, see note *)
  }

(**
   Here are some invariants of the pool:

   1°) every Ptr.t is present in the map vs if it is a VPtr.t
       and ts if it is a TPtr.t

   2°) Parents of a node are only significative and searched for
       nodes that have no link in the union-find map (i.e.,
       parents are unused if the node is present in the eq_map).

   3°) Term in the pool are kept in normal form. Any update that
       could trigger other normalisation has to be propagated.
       This is the role of the parent node.

       TODO #4: manage update of unification variables
 *)

let funptrs : anyfunptr FunHash.t = FunHash.create 256
let clsptrs : anyclsptr ClsHash.t = ClsHash.create 256

let reset_tbls () =
  Epsilon.reset_epsilons ();
  ClsHash.clear clsptrs;
  FunHash.clear funptrs

let print_parents ch pars =
  MapKey.iter (fun _ s ->
      PtrSet.iter (Printf.fprintf ch "%a " Ptr.print) s) pars

(** Find operation (with path contraction). *)
let find : Ptr.t -> pool -> Ptr.t = fun p po ->
  let rec follow p time =
    try
      let q = ptr_get p time in
      follow q time
    with Not_found -> p
  in
  follow p po.time

let find_valu : VPtr.t -> pool -> VPtr.t = fun p po ->
  let p = find (Ptr.V_ptr p) po in
  match p with
  | Ptr.V_ptr p -> p
  | Ptr.T_ptr _ -> assert false

(** Printing a pool (useful for debugging. *)
let print_pool : string -> out_channel -> pool -> unit = fun prefix ch po ->
  let { ts; vs; eq_map } = po in
  Printf.fprintf ch "%s#### Nodes ####\n" prefix;
  let fn (k, n) =
    let b = if Timed.get po.time k.Ptr.bs then "*" else "" in
    let pars = let p = find (Ptr.V_ptr k) po in ptr_par p po.time in
    Printf.fprintf ch "%s  %a%s\t→ %a [%a]\t\n" prefix VPtr.print k b
      print_v_node n print_parents pars
  in
  List.iter fn vs;
  Printf.fprintf ch "%s---------------\n" prefix;
  let fn (k, n) =
    let f = if Timed.get po.time k.Ptr.fs then "+" else "" in
    let g = if Timed.get po.time k.Ptr.ns then "n" else "" in
    let pars = let p = find (Ptr.T_ptr k) po in ptr_par p po.time in
    Printf.fprintf ch "%s  %a%s%s\t→ %a [%a]\t\n" prefix TPtr.print k f g
      print_t_node n print_parents pars
  in
  List.iter fn ts;
  Printf.fprintf ch "%s#### Links ####\n" prefix;
  let fn (p1, p2) =
    let p3 = ptr_get p1 po.time in
    Printf.fprintf ch "%s  %a\t→ %a (%a)\n" prefix
                   Ptr.print p1 Ptr.print p2 Ptr.print p3
  in
  List.iter fn eq_map;
  Printf.fprintf ch "%s###############" prefix


(** Initial, empty pool. *)
let empty_pool : unit -> pool = fun () ->
  { vs     = []
  ; ts     = []
  ; cvs    = []
  ; cts    = []
  ; os     = []
  ; next   = 0
  ; time   = Timed.Time.save ()
  ; ineq   = []
  ; eq_map = []
  ; values = []
  ; v_defs = []
  ; e_defs = []
  ; in_uni = []
  }

(** Node search. *)
let find_v_node : VPtr.t -> pool -> v_node = fun p po ->
  let open Ptr in
  match p.vval with
  | DP(V_Node, v) -> v
  | _ -> assert false

let find_t_node : TPtr.t -> pool -> t_node = fun p po ->
  let open Ptr in
  match p.tval with
  | DP(T_Node, v) -> v
  | _ -> assert false

(** Managment of the boolean fields in the various nodes *)
let get_bs : VPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.bs

let set_bs : VPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.bs true }

let get_ns : TPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.ns

let set_ns : TPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.ns true }

let get_fs : TPtr.t -> pool -> bool = fun p po ->
  let open Ptr in
  Timed.get po.time p.fs

let set_fs : TPtr.t -> pool -> pool = fun p po ->
  let open Ptr in
  { po with time = Timed.set po.time p.fs true }

let push_uni : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  { po with in_uni = (p1, p2) :: po.in_uni }

let test_uni : Ptr.t -> Ptr.t -> pool -> bool = fun p1 p2 po ->
  List.exists (fun (q1,q2) -> eq_ptr p1 q1 && eq_ptr p2 q2) po.in_uni

let pop_uni : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  match po.in_uni with
  | [] -> assert false
  | (q1, q2) :: in_uni ->
     assert (eq_ptr p1 q1);
     assert (eq_ptr p2 q2);
     { po with in_uni }

(** Geting the children sons of a node. *)

let children_bndr_closure
    : type a b. (a, b) bndr_closure -> (int -> par_key) ->
           int * (par_key * Ptr.t) list -> int * (par_key * Ptr.t) list
  = fun (_,vs,ts) fn (i0, acc) ->
    let res = ref acc in
    Array.iteri (fun i vptr -> res := (fn (i+i0), Ptr.V_ptr vptr) :: !res) vs;
    let i0 = i0 + Array.length vs in
    Array.iteri (fun i ptr -> res := (fn (i+i0), ptr) :: !res) ts;
    let i0 = i0 + Array.length ts in
    (i0, !res)

let children_closure
    : type a. a closure -> (int -> par_key) ->
           int * (par_key * Ptr.t) list -> int * (par_key * Ptr.t) list
  = fun (_,vs,ts) fn (i0, acc) ->
    let res = ref acc in
    Array.iteri (fun i vptr -> res := (fn (i+i0), Ptr.V_ptr vptr) :: !res) vs;
    let i0 = i0 + Array.length vs in
    Array.iteri (fun i ptr -> res := (fn (i+i0), ptr) :: !res) ts;
    let i0 = i0 + Array.length ts in
    (i0, !res)

let children_v_node : v_node -> (par_key * Ptr.t) list = fun n ->
  match n with
  | VN_HApp c     -> let HO(_,b,c) = c in
                     let kn n = KV_HApp n in
                     snd (children_closure b kn
                         (children_closure c kn (0, [])))
  | VN_LAbs(b,_)  -> let kn n = KV_LAbs n in
                     snd (children_bndr_closure b kn (0, []))
  | VN_Cons(a,pv) -> [(KV_Cons a.elt, Ptr.V_ptr pv)]
  | VN_Reco(m)    -> A.fold (fun a p s -> ((KV_Reco a, Ptr.V_ptr p)::s)) m []
  | VN_Defi _
  | VN_VWit _
  | VN_UWit _
  | VN_EWit _
  | VN_ESch _
  | VN_Goal _
  | VN_UVar _ (* TODO #4 check *)
  | VN_Vari _
  | VN_Scis       -> []

let children_t_node : t_node -> (par_key * Ptr.t) list = fun n ->
  match n with
  | TN_Valu(pv)    -> [(KT_Valu, Ptr.V_ptr pv)]
  | TN_Appl(pt,pu,_) -> [(KT_Appl `Right, pu); (KT_Appl `Left, pt)]
  | TN_Name(_,pt)  -> [(KT_Name, pt)]
  | TN_Proj(pv,l)  -> [(KT_Proj l.elt, Ptr.V_ptr pv)]
  | TN_Case(pv,cs) -> (KT_Case None, Ptr.V_ptr pv) ::
                        A.fold (fun a b acc ->
                            let kn n = KT_Case (Some (a, n)) in
                            snd (children_bndr_closure b kn (0,acc)))
                          cs []
  | TN_Delm(pt)    -> [(KT_Delm, pt)]
  | TN_FixY(b,_)   -> let kn n = KT_FixY n in
                      snd (children_bndr_closure b kn (0, []))
  | TN_MAbs b      -> let kn n = KT_MAbs n in
                      snd (children_bndr_closure b kn (0, []))
  | TN_HApp c      -> let HO(_,b,c) = c in
                      let kn n = KT_HApp n in
                      snd (children_closure b kn
                          (children_closure c kn (0,[])))
  | TN_UWit _
  | TN_EWit _
  | TN_ESch _
  | TN_Prnt _
  | TN_Goal _
  | TN_UVar _  (* TODO #4 check *)
  | TN_Vari _      -> []

(** Test if a term is "free", that is occures not only unser binder
    and therefore should be normalised. This is important for closure,
    if we normalise all closed subterm under binders, PML loops *)
let is_free : Ptr.t -> pool -> bool =
  fun p po ->
    let p = find p po in
    match p with
    | Ptr.V_ptr _ -> true
    | Ptr.T_ptr t -> get_fs t po

(** Test if a nobox *)
let is_nobox : Ptr.t -> pool -> bool =
  fun p po ->
    let p = find p po in
    match p with
    | Ptr.V_ptr t -> get_bs t po
    | Ptr.T_ptr _ -> false

(** Test if normal *)
let is_normal : Ptr.t -> pool -> bool =
  fun p po ->
    let p = find p po in
    match p with
    | Ptr.V_ptr _  -> true
    | Ptr.T_ptr tp -> get_ns tp po

(** Test for v_node that are always nobox *)
let immediate_nobox : v_node -> bool = function
  | VN_LAbs _
  | VN_Cons _
  | VN_Reco _
  | VN_Defi _
  | VN_Scis   -> true (* Check VN_Scis *)
  | VN_VWit _
  | VN_UWit _
  | VN_EWit _
  | VN_ESch _
  | VN_HApp _
  | VN_UVar _
  | VN_Goal _
  | VN_Vari _ -> false

(** Adding a parent to a given node. *)
let add_parent_nodes : Ptr.t -> (par_key * Ptr.t) list-> pool -> pool =
  fun np ps po ->
  let fn po (k, p) =
    let p = find p po in
    let time = ptr_add_par k np p po.time in
    { po with time }
  in
  List.fold_left fn po ps

let add_parent_v_nodes : VPtr.t -> (par_key * Ptr.t) list -> pool -> pool =
  fun vp ps po -> add_parent_nodes (Ptr.V_ptr vp) ps po

let add_parent_t_nodes : TPtr.t -> (par_key * Ptr.t) list -> pool -> pool =
  fun tp ps po -> add_parent_nodes (Ptr.T_ptr tp) ps po

(** Obtain the parents of a pointed node. *)
let parents : Ptr.t -> pool -> par_map = fun p po ->
  let p = find p po in
  ptr_par p po.time

(** union of parents (used when joining nodes) *)
let add_parents : Ptr.t -> par_map -> pool -> pool = fun p nps po ->
  let p = find p po in
  let time = ptr_union_pars nps p po.time in
  { po with time }

(** Equalities *)

(* NOTE: loose path shortening, not really a problem ? *)
let eq_vptr : pool -> VPtr.t -> VPtr.t -> bool = fun po p1 p2 ->
  let p1 = find_valu p1 po in
  let p2 = find_valu p2 po in
  VPtr.compare p1 p2 = 0

(* NOTE: loose path shortening, not really a problem ? *)
let eq_tptr : pool -> TPtr.t -> TPtr.t -> bool = fun po p1 p2 ->
  let p1 = find (Ptr.T_ptr p1) po in
  let p2 = find (Ptr.T_ptr p2) po in
  Ptr.compare p1 p2 = 0

(* NOTE: loose path shortening, not really a problem ? *)
let eq_ptr : pool -> Ptr.t -> Ptr.t -> bool = fun po p1 p2 ->
  let p1 = find p1 po in
  let p2 = find p2 po in
  eq_ptr p1 p2

let eq_ho_appl : type a. pool -> a ho_appl -> a ho_appl -> bool =
  fun po a1 a2 ->
    let open Eq in
    let (HO(s1,(f1,vf1,tf1),(e1,ve1,te1)),
         HO(s2,(f2,vf2,tf2),(e2,ve2,te2))) = (a1, a2) in
    match eq_sort s1 s2 with
    | Eq ->
       f1 == f2 && e1 == e2 &&
         Array.for_all2 (eq_vptr po) vf1 vf2 &&
           Array.for_all2 (eq_ptr po) tf1 tf2 &&
             Array.for_all2 (eq_vptr po) ve1 ve2 &&
               Array.for_all2 (eq_ptr po) te1 te2
    | NEq -> false

let eq_cl po s (f1,vs1,ts1 as _cl1) (f2,vs2,ts2 as _cl2) =
  if f1 == f2 then
    Array.for_all2 (eq_vptr po) vs1 vs2 &&
    Array.for_all2 (eq_ptr  po) ts1 ts2
  else
    ((*assert (not (eq_funptr s f1 f2) ||
               (Printf.printf "%a (%d)\n%a (%d)\n%!"
                               (pbcl s) _cl1 (hash_funptr s f1)
                               (pbcl s) _cl2 (hash_funptr s f2);
                false);*)
     false)

(** Equality functions on nodes. *)
let eq_v_nodes : pool -> v_node -> v_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    match (n1, n2) with
    | (VN_LAbs(b1,t1), VN_LAbs(b2,t2)) -> eq_cl po V b1 b2 && t1 = t2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) -> c1.elt = c2.elt && eq_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) -> A.equal (eq_vptr po) m1 m2
    | (VN_Defi(v1)   , VN_Defi(v2)   ) -> v1 == v2
    | (VN_Scis       , VN_Scis       ) -> true
    | (VN_VWit(w1)   , VN_VWit(w2)   ) -> w1.valu == w2.valu
    | (VN_UWit(w1)   , VN_UWit(w2)   ) -> w1.valu == w2.valu
    | (VN_EWit(w1)   , VN_EWit(w2)   ) -> w1.valu == w2.valu
    | (VN_ESch(i1,w1), VN_ESch(i2,w2)) -> i1 = i2 && w1.valu == w2.valu
    | (VN_HApp(e1)   , VN_HApp(e2)   ) -> eq_ho_appl po e1 e2
    | (VN_Goal(v1)   , VN_Goal(v2)   ) -> eq_expr v1 v2
    | (VN_UVar(v1)   , VN_UVar(v2)   ) -> v1.uvar_key = v2.uvar_key
    | (_             , _             ) -> false

let eq_t_nodes : pool -> t_node -> t_node -> bool =
  fun po n1 n2 -> n1 == n2 ||
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) -> eq_vptr po p1 p2
    | (TN_Appl(p11,p12,_), TN_Appl(p21,p22,_)) ->
                                              eq_ptr po p11 p21
                                              && eq_ptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) -> eq_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) -> eq_expr s1 s2
                                              && eq_ptr po p1 p2
    | (TN_Delm(p1)     , TN_Delm(p2)     ) -> eq_ptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) -> eq_vptr po p1 p2
                                              && l1.elt = l2.elt
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) -> eq_vptr po p1 p2
                                              && A.equal (eq_cl po V) m1 m2
    | (TN_FixY(b1,_)   , TN_FixY(b2,_)   ) -> eq_cl po Sorts.T b1 b2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) -> s1 = s2
    | (TN_UWit(w1)     , TN_UWit(w2)     ) -> w1.valu == w2.valu
    | (TN_EWit(w1)     , TN_EWit(w2)     ) -> w1.valu == w2.valu
    | (TN_ESch(i1,w1)  , TN_ESch(i2,w2)  ) -> i1 = i2 && w1.valu == w2.valu
    | (TN_HApp(e1)     , TN_HApp(e2)     ) -> eq_ho_appl po e1 e2
    | (TN_Goal(t1)     , TN_Goal(t2)     ) -> eq_expr t1 t2
    | (TN_UVar(v1)     , TN_UVar(v2)     ) -> v1.uvar_key = v2.uvar_key
    | (_               , _               ) -> false


(** Insertion function for nodes. *)
exception FoundV of VPtr.t * pool
let insert_v_node : v_node -> pool -> VPtr.t * pool = fun nn po ->
  let children = children_v_node nn in
  try
    (** search if the node already exists, using parents if possible *)
    match children with
    | [] ->
       let fn (p, n) = if eq_v_nodes po n nn then raise (FoundV (p,po)) in
       List.iter fn po.cvs; raise Not_found
    | (k,n)::l ->
       let f k n = MapKey.find k (parents n po) in
       let possible =
         List.fold_left (fun acc (k, n) -> PtrSet.inter (f k n) acc) (f k n) l
       in
       let fn po n =
         match n with
         | Ptr.V_ptr n ->
            let node = find_v_node n po in
            if eq_v_nodes po node nn then raise (FoundV (n,po))
         | Ptr.T_ptr n -> ()
       in
       PtrSet.iter (fn po) possible;
       raise Not_found
  with
  | FoundV(p,po) -> (p, po)
  | Not_found ->
     (** new node creation *)
     let open Ptr in
     let ptr = { vadr = po.next
               ; vlnk = Timed.tref (Par MapKey.empty)
               ; bs   = Timed.tref (immediate_nobox nn)
               ; vval = DP(V_Node, nn); vas = [] } in
     let vs = (ptr,nn) :: po.vs in
     let cvs = if children = [] then (ptr,nn) :: po.cvs else po.cvs in
     let next = po.next + 1 in
     let po = { po with vs ; cvs; next } in
     let po = add_parent_v_nodes ptr children po in
     (ptr, po)

exception FoundT of TPtr.t * pool

let insert_t_node : bool -> t_node -> pool -> TPtr.t * pool =
  fun fs nn po ->
    let children = children_t_node nn in
    try
      (** search if the node already exists, using parents if possible *)
      match children with
      | [] ->
         let fn (p, n) = if eq_t_nodes po n nn then raise (FoundT (p,po)) in
         List.iter fn po.cts; raise Not_found
      | (k,n)::l ->
         let f k n = MapKey.find k (parents n po) in
         let possible =
           let fn acc (k,n) = PtrSet.inter (f k n) acc in
           List.fold_left fn (f k n) l
         in
         let fn po n =
           match n with
           | Ptr.V_ptr _ -> ()
           | Ptr.T_ptr n ->
              let node = find_t_node n po in
              if eq_t_nodes po node nn then raise (FoundT (n,po));
         in
         PtrSet.iter (fn po) possible;
         raise Not_found
    with
    | FoundT(p, po) ->
       (** if the node is found but was not free (was under binders),
           then it may become free if the equal added node is free *)
       let po =
         if fs then begin
             let p' = find (Ptr.T_ptr p) po in
             match p' with
             | Ptr.T_ptr p' -> set_fs p' po
             | _ -> po
           end
         else po
       in (p, po)
    | Not_found ->
       (** new node creation *)
       let open Ptr in
       let ptr = { tadr = po.next
                 ; tlnk = Timed.tref (Par MapKey.empty)
                 ; ns   = Timed.tref false
                 ; fs   = Timed.tref fs
                 ; tval = DP(T_Node, nn)
                 ; tas  = [] } in
       let ts = (ptr, nn) :: po.ts in
       let cts = if children = [] then (ptr, nn) :: po.cts else po.cts in
       let time, eq_map =
         match nn with
         | TN_Valu(pv) -> let tp = Ptr.T_ptr ptr and vp = Ptr.V_ptr pv in
                          let time = Timed.set po.time ptr.ns true in
                          (ptr_set tp vp time, (tp,vp)::po.eq_map)
         | _           -> (po.time, po.eq_map)
       in
       let next= po.next + 1 in
       let po = { po with time; ts ; cts; next; eq_map } in
       let po = add_parent_t_nodes ptr children po in
       (ptr, po)

let insert_v_node nn po = Chrono.add_time inser_chrono (insert_v_node nn) po
let insert_t_node nn po = Chrono.add_time inser_chrono (insert_t_node nn) po

(** avoid UWit and EWit, that makes duplicate. However, UWit and EWit
    can still appear as sub terms.
    - Also excludes unset uvar.
    - and case with only one case (temporary fix to avoid subtyping
      witness) *)
let rec not_uewit : type a. a ex loc -> bool =
  fun e ->
    match (Norm.whnf e).elt with
    | UWit _    -> false
    | EWit _    -> false
    | VPtr _    -> false
    | TPtr _    -> false
    | Valu e    -> not_uewit e
    | Case(_,c) -> A.length c > 1 (* TODO #29: fix this issue and remove! *)
    | _         -> true

(** Unification of terms in the pool *)
exception NoUnif

let keep_intermediate = ref false
let use_eval          = ref true

module VPtrSet = Set.Make(VPtr)

let test_cyclic po pv =
  let adone = ref VPtrSet.empty in
  let rec fn above pv =
    let pv = find_valu pv po in
    if VPtrSet.mem pv above then raise Contradiction;
    if VPtrSet.mem pv !adone then () else
      begin
        let above = VPtrSet.add pv above in
        adone := VPtrSet.add pv !adone;
        let n = find_v_node pv po in
        match n with
        | VN_Cons(s,pv) -> fn above pv
        | VN_Reco(m)    -> A.iter (fun _ -> fn above) m
        | _             -> ()
      end
  in
  fn VPtrSet.empty pv

(** Insertion and normalisation of actual terms and values to the pool. *)
let rec add_term :  bool -> bool -> pool -> term
                    -> Ptr.t * pool = fun o free po t0 ->
  let t = Norm.whnf t0 in
  match Timed.get po.time t0.usr with
  | NPtr p | BPtr(_,p) when free      -> (find p po, po)
  | UPtr p | BPtr(p,_) when not free  -> (find p po, po)
  | UPtr p             when free      -> normalise p po
  | EPtr _ -> assert false
  | _      ->
  let add_term = add_term o free in
  let add_valu = add_valu o in
  let insert node po =
    if free then
      begin
        if !keep_intermediate then
          begin
            let (p, po) = insert_t_node true node po in
            let (q, po) = normalise_t_node ~old:p node po in
            (find q po, po)
          end
        else
          normalise_t_node node po
      (* NOTE: insrting not normal term as can be faster by avoiding
         renormalising the same terms, but in case of big computation, the
         size of the pool may explode, hence a choice fr the user *)
      end
    else
      begin
        let (p, po) = insert_t_node false node po in
        (find (Ptr.T_ptr p) po, po)
      end
  in
  (*log_edp2 "add_term %b %a" free Print.ex t0;*)
  let (p, po) =
    match t.elt with
    | Valu(v)     -> let (pv, po) = add_valu po v in
                     insert (TN_Valu(pv)) po
    | Appl(t,u,l) -> let (pt, po) = add_term po t in
                     let (pu, po) = add_term po u in
                     insert (TN_Appl(pt,pu,l)) po
    | MAbs(b)     -> let (cl, po) = add_bndr_closure po S T o b in
                     insert (TN_MAbs(cl)) po
    | Name(s,t)   -> let (pt, po) = add_term po t in
                     insert (TN_Name(s,pt)) po
    | Proj(v,l)   -> let (pv, po) = add_valu po v in
                     insert (TN_Proj(pv,l)) po
    | Case(v,m)   -> let (pv, po) = add_valu po v in
                     let (m,  po) =
                       let fn _ (_,x) po = add_bndr_closure po V T o x in
                       A.fold_map fn m po
                     in
                     insert (TN_Case(pv,m)) po
    | FixY(b)     -> let (cl, po) = add_bndr_closure po T V o b in
                     let ptr = Timed.tref Prep in
                     let (pt, po) = insert_t_node free (TN_FixY(cl,ptr)) po in
                     let pt = Ptr.T_ptr pt in
                     let po =
                       { po with time = Timed.set po.time ptr (Init pt) }
                     in
                     if free then normalise pt po else (find pt po, po)
    | Prnt(s)     -> insert (TN_Prnt(s)) po
    | Repl(_,u)   -> add_term po u
    | Delm(u)     -> let (pt, po) = add_term po u in
                     insert (TN_Delm(pt)) po
    | Hint(h,t)   -> (match h with
                      | Close _
                      | Auto  _
                      | LSet  _
                      | Sugar   -> add_term po t
                      | Eval    ->
                         try
                           if not !use_eval then raise Exit;
                           let open Erase in
                           let open Eval in
                           let t = Pos.in_pos t.pos
                                     (Valu (to_valu (eval (term_erasure t))))
                           in
                           add_term po t
                         with
                           Erase.Erasure_error _ | Exit -> add_term po t)
    | Coer(_,t,_) -> add_term po t
    | Such(_,_,r) -> add_term po (bseq_open r.binder)
    | UWit(w)     -> insert (TN_UWit(w)) po
    | EWit(w)     -> insert (TN_EWit(w)) po
    | ESch(T,i,w) -> insert (TN_ESch(i,w)) po
    | HApp(s,f,a) -> let (hoa, po) = add_ho_appl po s f a in
                     insert (TN_HApp(hoa)) po
    | HDef(_,d)   -> let (pt, po) =
                     try (List.assq d po.e_defs, po)
                     with Not_found ->
                       let (pt,po) = add_term po d.expr_def in
                       let po = { po with e_defs = (d,pt)::po.e_defs } in
                       (pt, po)
                     in
                     if free then normalise pt po else (find pt po, po)
    | UVar(_,v)   -> insert (TN_UVar(v)) po
    | Goal(_)     -> insert (TN_Goal(t)) po
    | Vari(s,x)   -> insert (TN_Vari(x)) po
    | TPtr(pt)    -> if free then normalise pt po else (find pt po, po)
    | ITag(_,n)   -> invalid_arg "itag in terms forbidden"
    | FixM(_)     -> invalid_arg "mu in terms forbidden"
    | FixN(_)     -> invalid_arg "nu in terms forbidden"
  in
  let po =
    if o && not_uewit t0 then
      { po with os = (p, t0)::po.os }
    else po
  in
  let po =
    let time =
      match (free, Timed.get po.time t0.usr) with
      | (true , Nothing) -> Timed.set po.time t0.usr (NPtr p)
      | (false, Nothing) -> Timed.set po.time t0.usr (UPtr p)
      | (true , UPtr q ) -> Timed.set po.time t0.usr (BPtr(q,p))
      | (false, NPtr q ) -> Timed.set po.time t0.usr (BPtr(p,q))
      | (_    , EPtr _ ) -> assert false
      | (_    , _      ) -> po.time (* node was recursively added ?*)

    in { po with time }
  in
  (p, po)

and     add_valu : bool -> pool -> valu -> VPtr.t * pool = fun o po v0 ->
  let add_valu = add_valu o in
  (*log_edp2 "add_valu %a" Print.ex v;*)
  let v = Norm.whnf v0 in
  match Timed.get po.time v0.usr with
  | EPtr p -> (p, po)
  | BPtr _ | NPtr _ | UPtr _  -> assert false
  | _      ->
  let (p,po) =
    match v.elt with
    | LAbs(_,b,t) -> let (b, po) = add_bndr_closure po V T o b in
                     insert_v_node (VN_LAbs(b,t)) po
    | Cons(c,v)   -> let (pv, po) = add_valu po v in
                     let (pv, po as r) = insert_v_node (VN_Cons(c,pv)) po in
                     test_cyclic po pv;
                     r
    | Reco(m)     -> let fn l (_, v) (m, po) =
                       let (pv, po) = add_valu po v in
                       (A.add l pv m, po)
                     in
                     let (m, po) = A.fold fn m (A.empty, po) in
                     let (pv, po as r) = insert_v_node (VN_Reco(m)) po in
                     test_cyclic po pv;
                     r
    | Scis        -> insert_v_node VN_Scis po
    | VDef(d)     -> begin
                       let cl = Timed.get po.time d.value_clos in
                       if cl then
                         insert_v_node (VN_Defi(d)) po
                       else try (List.assq d po.values, po)
                       with Not_found ->
                         let (pv,po) = add_valu po d.value_eras in
                         let po = { po with values = (d,pv)::po.values } in
                         (pv, po)
                     end
    | Coer(_,v,_) -> add_valu po v
    | Such(_,_,r) -> add_valu po (bseq_open r.binder)
    | VWit(w)     -> insert_v_node (VN_VWit(w)) po
    | UWit(w)     -> insert_v_node (VN_UWit(w)) po
    | EWit(w)     -> insert_v_node (VN_EWit(w)) po
    | ESch(v,i,w) -> insert_v_node (VN_ESch(i,w)) po
    | HApp(s,f,a) -> let (hoa, po) = add_ho_appl po s f a in
                     insert_v_node (VN_HApp(hoa)) po
    | HDef(_,d)   -> begin
                       try (List.assq d po.v_defs, po)
                       with Not_found ->
                         let (pv,po) = add_valu po d.expr_def in
                         let po = { po with v_defs = (d,pv)::po.v_defs } in
                         (pv, po)
                     end
    | UVar(_,v)   -> insert_v_node (VN_UVar(v)) po
    | Goal(_)     -> insert_v_node (VN_Goal(v)) po
    | VPtr(pv)    -> (pv, po)
    | Vari(v,x)   -> insert_v_node (VN_Vari(x)) po
    | ITag(_,n)   -> invalid_arg "itag in values forbidden"
    | FixM(_)     -> invalid_arg "mu in values forbidden"
    | FixN(_)     -> invalid_arg "nu in values forbidden"
  in
  let po =
    if o && not_uewit v0 then
      { po with os = (Ptr.V_ptr p, Pos.none (Valu v0))::po.os }
    else po
  in
  let po = {po with time = Timed.set po.time v0.usr (EPtr p)} in
  (p, po)

(** case of closure for binder *)
and add_bndr_closure : type a b. pool -> a sort -> b sort ->
                       bool -> (a, b) bndr -> (a, b) bndr_closure * pool =
  fun po sa sr o b ->
    let (funptr, vs, ts as cl) = Closures.make_bndr_closure sa b in
    let po = ref po in
    let vs = Array.map (fun v -> let (vptr,p) = add_valu o !po v in
                                 po := p; vptr) vs
    in
    let ts = Array.map (fun t -> let (tptr,p) = add_term o false !po t in
                                 po := p; tptr) ts
    in
    let po = !po in
    let key = T(sa,sr,funptr) in
    try
      let T(sa',sr',funptr') = FunHash.find funptrs key in
      match eq_sort sa sa', eq_sort sr sr' with
      | Eq.Eq, Eq.Eq -> ((funptr',vs,ts), po)
      | _ -> assert false
    with Not_found ->
      FunHash.add  funptrs key key;
      ((funptr,vs,ts), po)

(** case of closure for hight order terms *)
and add_ho_appl
    : type a b. pool -> a sort -> (a -> b) ex loc
           -> a ex loc -> b ho_appl * pool
  = fun po se f e ->
    let (sf, f) = sort f in
    let (f, vf, tf as cf) = Closures.make_closure f in
    let (e, ve, te as ce) = Closures.make_closure e in
    let po = ref po in
    let vf = Array.map (fun v -> let (vptr,p) = add_valu false !po v in
                                 po := p; vptr) vf
    in
    let tf = Array.map (fun t -> let (ptr,p) = add_term false false !po t in
                                 po := p; ptr) tf
    in
    let ve = Array.map (fun v -> let (vptr,p) = add_valu false !po v in
                                 po := p; vptr) ve
    in
    let te = Array.map (fun t -> let (ptr,p) = add_term false false !po t in
                                 po := p; ptr) te
    in
    let po = !po in
    let key = C(sf, f) in
    let f : unit -> (a -> b) clsptr = fun () ->
      try
        let C(sf',f') = ClsHash.find clsptrs key in
        match eq_sort sf sf' with
        | Eq.Eq -> f'
        | _ -> assert false
      with Not_found ->
        ClsHash.add clsptrs key key;
        f
    in
    let key = C(se,e) in
    let e : unit -> a clsptr = fun () ->
      try
        let C(se',e') = ClsHash.find clsptrs key in
        match eq_sort se se' with
        | Eq.Eq -> e'
        | _ -> assert false
      with Not_found ->
        ClsHash.add clsptrs key key;
        e
    in
    (HO(se,(f (),vf,tf),(e (),ve,te)), po)

(** Normalisation function for pointer *)
and normalise : Ptr.t -> pool -> Ptr.t * pool =
  fun p0 po ->
    match p0 with
    | Ptr.V_ptr _ -> (p0, po)
    | Ptr.T_ptr p ->
       if get_ns p po then
         (find p0 po, po)
       else
         begin
           let (tp, po) = normalise_t_node ~old:p (find_t_node p po) po in
           (find tp po, po)
         end

(** Normalisation function for nodes *)
and normalise_t_node : ?old:TPtr.t -> t_node -> pool -> Ptr.t  * pool =
  fun ?old node po ->
    let insert node po =
      match old with
      | None   -> let (p, po) = insert_t_node true node po in
                  (find (Ptr.T_ptr p) po, po)
      | Some p -> let p = find (Ptr.T_ptr p) po in
                  let po =
                    match p with
                    | Ptr.V_ptr _ -> po
                    | Ptr.T_ptr p -> set_fs p po
                  in
                  (p, po)
    in
    let set_ns po =
      match old with
      | None   -> po
      | Some p -> set_ns p po
    in
    let union tp po =
      match old with
      | None -> po
      | Some p -> union (Ptr.T_ptr p) tp po
    in
    let (p, po) = match node with
      | TN_Valu(pv)    -> let po = set_ns po in
                          (find (Ptr.V_ptr pv) po, po)
      | TN_Appl(pt,pu,l) ->
         begin
           log_edp2 "normalise in %a = TN_Appl: %a %a"
             print_t_node node Ptr.print pt Ptr.print pu;
           let (pt, po) = normalise pt po in
           let (pu, po) = normalise pu po in
           let (save, nb) = get_loop pt pu in
           set_loop pt pu (nb+1);
           try if nb > 10 then raise Exit;
               match (pt, pu) with
           | (Ptr.V_ptr pf, Ptr.V_ptr pv) ->
              begin
                match find_v_node pf po, get_bs pv po with
                | VN_LAbs(b,l'), true        ->
                   begin
                     assert (l = l');
                     let b = subst_closure b in
                     let t = bndr_subst b (VPtr pv) in
                     let po = set_ns po in
                     let (tp, po) = add_term false true po t in
                     let po = union tp po in
                     restore_loop pt save;
                     log_edp2 "normalised in %a = TN_Appl Lambda %a %a => %a"
                          print_t_node node Ptr.print pt Ptr.print pu
                          Ptr.print tp;
                     (tp,po)
                   end
                | _          ->
                   raise Exit
              end
           | (_           , _           ) -> raise Exit
           with Exit ->
             restore_loop pt save;
             let (tp, po) = insert (TN_Appl(pt,pu,l)) po in
             (* NOTE: testing tp in po.ns seems incomplete *)
             log_edp2 "normalised in %a = TN_Appl Appl: %a %a => %a"
               print_t_node node Ptr.print pt Ptr.print pu Ptr.print tp;
             (tp, po)
         end
      | TN_MAbs(b)     -> insert node po (* FIXME #7 can do better. *)
      | TN_Name(s,pt)  -> insert node po (* FIXME #7 can do better. *)
      | TN_Delm(tp)    ->
         begin
           let tp = find tp po in
           if is_nobox tp po then
             let po = union tp po in
             (tp, po)
           else
             insert node po
         end
      | TN_Proj(pv0,l) ->
         begin
           let pv = find_valu pv0 po in
           log_edp2 "normalisation in %a = TN_Proj %a"
                print_t_node node VPtr.print pv0;
           match find_v_node pv po with
           | VN_Reco(m) ->
              begin
                try
                  let tp = find (Ptr.V_ptr (A.find l.elt m)) po in
                  let po = set_ns po in
                  let po = union tp po in
                  log_edp2 "normalised in %a = TN_Proj %a => %a"
                       print_t_node node VPtr.print pv0 Ptr.print tp;
                  (tp, po)
                with Not_found -> insert node po
              end
           | _          -> insert node po
         end
      | TN_Case(pv0,m) ->
         begin
           let pv = find_valu pv0 po in
           log_edp2 "normalisation in %a = TN_Case %a"
                print_t_node node VPtr.print pv0;
           try
             match find_v_node pv po with
             | VN_Cons(c,pv) ->
                let b = subst_closure (A.find c.elt m) in
                let t = bndr_subst b (VPtr pv) in
                let po = set_ns po in
                let (tp, po) = add_term false true po t in
                let po = union tp po in
                log_edp2 "normalised in %a = TN_Case %a => %a"
                     print_t_node node VPtr.print pv0 Ptr.print tp;
                (tp,po)
             | _            -> raise Not_found
           with Not_found ->
             log_edp2 "normalisation no progress %a = TN_Case: %a"
                  print_t_node node VPtr.print pv0;
             insert node po
         end
      | TN_FixY(f,ptr) ->
         begin
           match Timed.get po.time ptr with
           | Prep    -> assert false
           | Init pt ->
              log_edp2 "normalisation in %a = TN_FixY" print_t_node node;
              let f = subst_closure f in
              let po = set_ns po in
              let (pv, po) = add_valu false po (bndr_subst f (TPtr pt)) in
              let pv = Ptr.V_ptr pv in
              let po = union pv po in
              log_edp2 "normalisation in %a = TN_FixY => %a"
                   print_t_node node Ptr.print pv;
              (pv, po)
         end
      | TN_UVar(v)   ->
         begin
           match !(v.uvar_val) with
           | Unset _ -> insert node po
           | Set t   -> let po = set_ns po in
                        let (tp, po) = add_term false true po t in
                        let po = union tp po in
                        (tp, po)
         end
      | TN_Prnt(_)
      | TN_UWit(_)
      | TN_EWit(_)
      | TN_ESch(_)
      | TN_HApp(_)
      | TN_Goal(_)
      | TN_Vari(_)    -> let po = set_ns po in
                         insert node po
    in
    (find p po, po)

(** test if to pointers just became equal and call union if it is the case *)
and check_eq : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  if eq_ptr po p1 p2 then po else
    match (p1, p2) with
    | Ptr.V_ptr vp1, Ptr.V_ptr vp2 ->
       let n1 = find_v_node vp1 po in
       let n2 = find_v_node vp2 po in
       if eq_v_nodes po n1 n2 then union p1 p2 po else po
    | Ptr.T_ptr tp1, Ptr.T_ptr tp2 ->
       let n1 = find_t_node tp1 po in
       let n2 = find_t_node tp2 po in
       if eq_t_nodes po n1 n2 then union p1 p2 po else po
    | _ -> po

(** check all equalities of two parent sets *)
and check_parents_eq pp1 pp2 po =
  let po = ref po in
  let fn k pp1 pp2 = match (pp1, pp2) with
    | (Some pp1, Some pp2) ->
       po := PtrSet.fold (fun p1 po ->
                 PtrSet.fold (fun p2 po ->
                     check_eq p1 p2 po) pp2 po) pp1 !po;
       None
    | ( _      , _       ) -> None
  in
  Chrono.add_time pareq_chrono
                  (fun () -> ignore (MapKey.merge fn pp1 pp2); !po) ()

(** reinsert a node that could be normalised *)
and reinsert : Ptr.t -> pool -> pool = fun p po ->
  let is_free = is_free p po in
  match p with
  | Ptr.T_ptr tp ->
     if is_free then snd (normalise p po)
     else
       begin
         let n1 = find_t_node tp po in
         match n1 with
         | TN_UVar({uvar_val = {contents = Set v}}) ->
            let (tp,po) = add_term false is_free po v in
            join p tp po
         | _ -> po
       end
  | Ptr.V_ptr vp ->
     let n1 = find_v_node vp po in
     begin
       match n1 with
       | VN_UVar({uvar_val = {contents = Set v}}) ->
          let (vp,po) = add_valu false po v in
          join p (Ptr.V_ptr vp) po
       | VN_Defi(v) when not (Timed.get po.time v.value_clos) ->
          let (vp,po) = add_valu false po v.value_eras in
          join p (Ptr.V_ptr vp) po
       | _ -> po
     end

(** reinsert values whose defs have just be opened *)
and reinsert_vdef : value list -> pool -> pool = fun vs po ->
  let fn (p, n) = List.exists (fun v -> eq_v_nodes po n (VN_Defi(v))) vs in
  let ptrs = List.filter fn po.vs in
  List.fold_left (fun po (p,n) -> reinsert (Ptr.V_ptr p) po) po ptrs

and check_ineq pool =
  (* NOTE: we could consider ineq as parents to avoid scanning the whole ineq
     list *)
  let fn (ineq,po) (pt, pu) =
    let pt = find pt po in
    let pu = find pu po in
    try
      ignore (UTimed.apply (unif_ptr po pt) pu);
      log_edp2 "add_inequiv: contradiction found";
      bottom ()
    with NoUnif -> ((pt,pu)::ineq, po)
  in
  let (ineq,pool) = List.fold_left fn ([], pool) pool.ineq in
  { pool with ineq }

(** Low level union operation. *)
(** is called directly ONLY for TN_UVar and VN_UVar, when we detect
    they are set, otherwise it loops *)
and join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  assert (not_lnk p1 po.time);
  assert (not_lnk p2 po.time);
  let nps = parents p1 po in
  let pp2 = parents p2 po in
  let po = add_parents p2 nps po in
  let fs2 = is_free p2 po in
  let fs1 = is_free p1 po in
  let bs2 = is_nobox p2 po in
  let bs1 = is_nobox p1 po in
  let po = { po with time = ptr_set p1 p2 po.time
                   ; eq_map = (p1,p2) :: po.eq_map }
  in
  begin
    match p1, p2 with
    | (Ptr.V_ptr pv1, Ptr.V_ptr pv2) -> test_cyclic po pv2
    | (_            , _            ) -> ()
  end;
  let po = if fs1 && not fs2 then begin
               match p2 with
               | Ptr.T_ptr p2 -> set_fs p2 po
               | Ptr.V_ptr _  -> assert false
             end
           else po
  in
  let po = if bs1 && not bs2 then begin
               let po = mk_eq_delim p2 po in
               match p2 with
               | Ptr.V_ptr p2 -> set_bs p2 po
               | Ptr.T_ptr _  -> assert false
             end
           else po
  in
  let po = check_parents_eq nps pp2 po in
  let po = MapKey.fold (fun k l po ->
               if is_head k then PtrSet.fold reinsert l po else po) nps po in
  let po = check_ineq po in
  po

and mk_eq_delim p po =
  List.fold_left (fun po (pt,nn) ->
      match nn with
      | TN_Delm pu when eq_ptr po (Ptr.T_ptr pt) p ->
         union (T_ptr pt) pu po
      | _ -> po
    ) po po.ts

(* when the join can be arbitrary, better to point to
   the oldest pointer (likely to given less occur-check failure*)
and age_join : Ptr.t -> Ptr.t -> pool -> pool = fun p1 p2 po ->
  if p2 < p1 then join p1 p2 po else join p2 p1 po

(** high level union doing all necessary check/cases *)
and union : ?no_rec:bool -> Ptr.t -> Ptr.t -> pool -> pool =
  fun ?(no_rec=false) p1 p2 po ->
  let p1 = find p1 po in
  let p2 = find p2 po in
  if eq_ptr po p1 p2 then po else
    match (p1, p2) with
    | (Ptr.T_ptr _  , Ptr.V_ptr _  ) -> join p1 p2 po
    | (Ptr.V_ptr _  , Ptr.T_ptr _  ) -> join p2 p1 po
    | (Ptr.T_ptr _  , Ptr.T_ptr _  ) -> age_join p1 p2 po
    | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
       begin
         let n1 = find_v_node vp1 po in
         let n2 = find_v_node vp2 po in
         match (n1, n2) with
         (* Immediate contradictions. *)
         | (VN_LAbs(_)     , VN_Reco(_)     )
           | (VN_LAbs(_)     , VN_Cons(_,_)   )
           | (VN_Reco(_)     , VN_LAbs(_)     )
           | (VN_Reco(_)     , VN_Cons(_,_)   )
           | (VN_Cons(_,_)   , VN_Reco(_)     )
           | (VN_Cons(_,_)   , VN_LAbs(_)     ) -> bottom ()
         (* Constructors. *)
         | (VN_Cons(c1,vp1), VN_Cons(c2,vp2)) ->
            if c1.elt <> c2.elt then bottom ();
            let po = age_join p1 p2 po in
            if no_rec then po else union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) po
         (* Records. *)
         | (VN_Reco(m1)    , VN_Reco(m2)    ) ->
            let po = ref (age_join p1 p2 po) in
            let test vp1 vp2 =
              po := union (Ptr.V_ptr vp1) (Ptr.V_ptr vp2) !po; true
            in
            if not no_rec && not (A.equal test m1 m2) then bottom ();
            !po
         (* Prefer real values as equivalence class representatives. *)
         | (VN_LAbs(_)     , VN_LAbs(_)     ) -> age_join p1 p2 po
         | (VN_LAbs(_)     , _              )     (* FIXME #22 *)
         | (VN_Reco(_)     , _              )
         | (VN_Cons(_,_)   , _              ) -> join p2 p1 po
         | (_              , VN_LAbs(_)     )
         | (_              , VN_Reco(_)     )
         | (_              , VN_Cons(_,_)   ) -> join p1 p2 po
         (* nobox or age_join otherwise. *)
         | (_              , _              ) ->
            match (get_bs vp1 po, get_bs vp2 po) with
            | (true, false) -> join p2 p1 po
            | (false, true) -> join p1 p2 po
            | (_    , _   ) -> age_join p2 p1 po
       end

(** Obtain the canonical term / value pointed by a pointer.
    Now only use to instanciate a unification variable. *)
(* NOTE: the "clos" bool is here to not follow the union find map if
    under closure, otherwise if loops, for instance on "exp n" *)
and canonical_term : bool -> TPtr.t -> pool -> term * pool
  = fun clos p po ->
  let p = if clos then Ptr.T_ptr p else find (Ptr.T_ptr p) po in
  let cv = canonical_valu clos in
  let cp = canonical      clos in
  match p with
  | Ptr.T_ptr(p) ->
     begin
        let t = find_t_node p po in
        (*log_edp2 "canonical_term %a = %a" TPtr.print p print_t_node t;*)
        match t with
        | TN_Valu(pv)    -> let (v, po) = cv pv po in
                            (Pos.none (Valu(v)), po)
        | TN_Appl(pt,pu,l) -> let (t, po) = cp pt po in
                            let (u, po) = cp pu po in
                            (Pos.none (Appl(t,u,l)), po)
        | TN_MAbs(b)     -> let (b, po) = canonical_bndr_closure b po in
                            (Pos.none (MAbs(b)), po)
        | TN_Name(s,pt)  -> let (t, po) = cp pt po in
                            (Pos.none (Name(s,t)), po)
        | TN_Delm(pt)    -> let (t, po) = cp pt po in
                            (Pos.none (Delm(t)), po)
        | TN_Proj(pv,l)  -> let (v, po) = cv pv po in
                            (Pos.none (Proj(v,l)), po)
        | TN_Case(pv,m)  -> let (v, po) = cv pv po in
                            let (m, po) = A.fold_map (fun _ b po ->
                              let (p, po) = canonical_bndr_closure b po in
                              ((no_pos, p), po)) m po
                            in
                            (Pos.none (Case(v, m)), po)
        | TN_FixY(b,_)   -> let (b, po) = canonical_bndr_closure b po in
                            (Pos.none (FixY(b)), po)
        | TN_Prnt(s)     -> (Pos.none (Prnt(s)), po)
        | TN_UWit(w)     -> (Pos.none (UWit(w)), po)
        | TN_EWit(w)     -> (Pos.none (EWit(w)), po)
        | TN_ESch(i,w)   -> (Pos.none (ESch(T,i,w)), po)
        | TN_HApp(e)     -> let HO(s,f,a) = e in
                            let (f, po) = canonical_closure f po in
                            let (a, po) = canonical_closure a po in
                            (Pos.none (HApp(s,f,a)), po)
        | TN_UVar(v)     -> begin
                              match !(v.uvar_val) with
                              | Unset _ -> (Pos.none (UVar(T,v)), po)
                              | Set t   ->
                                  let (tp, po) = add_term false false po t in
                                  let po = join (Ptr.T_ptr p) tp po in
                                  cp tp po
                            end
        | TN_Vari(x)     -> (Pos.none (Vari(T,x)), po)
        | TN_Goal(t)     -> (t, po)
      end
  | Ptr.V_ptr(p) ->
      let (v, po) = cv p po in
      (Pos.none (Valu(v)), po)

(* NOTE: the "clos" bool is here to not follow the union find map if
    under closure, otherwise if loops, for instance on "exp n" *)
and     canonical_valu : bool -> VPtr.t -> pool -> valu * pool
= fun clos p po ->
  let p = if clos then p else find_valu p po in
  let cv = canonical_valu clos in
  let v = find_v_node p po in
  (*log_edp2 "canonical_term %a = %a" VPtr.print p print_v_node v;*)
  match v with
  | VN_LAbs(b,t)   -> let (b, po) = canonical_bndr_closure b po in
                      (Pos.none (LAbs(None, b, t)), po)
  | VN_Cons(c,pv)  -> let (v, po) = cv pv po in
                      (Pos.none (Cons(c,v)), po)
  | VN_Reco(m)     -> let fn l pv (m, po) =
                        let (v, po) = cv pv po in
                        (A.add l (no_pos,v) m, po)
                      in
                      let (m, po) = A.fold fn m (A.empty, po) in
                      (Pos.none (Reco(m)), po)
  | VN_Defi(v)     -> (Pos.none (VDef(v)), po)
  | VN_Scis        -> (Pos.none Scis, po)
  | VN_VWit(w)     -> (Pos.none (VWit(w)), po)
  | VN_UWit(w)     -> (Pos.none (UWit(w)), po)
  | VN_EWit(w)     -> (Pos.none (EWit(w)), po)
  | VN_ESch(i,w)   -> (Pos.none (ESch(V,i,w)), po)
  | VN_HApp(e)     -> let HO(s,f,a) = e in
                      let (f, po) = canonical_closure f po in
                      let (a, po) = canonical_closure a po in
                      (Pos.none (HApp(s,f,a)), po)
  | VN_UVar(v)     -> begin
                        match !(v.uvar_val) with
                        | Unset _ -> (Pos.none (UVar(V,v)), po)
                        | Set w   ->
                           let (vp, po) = add_valu false po w in
                           let po = join (Ptr.V_ptr p)
                                      (Ptr.V_ptr vp) po
                           in
                           cv vp po
                      end
  | VN_Vari(x)     -> (Pos.none (Vari(V,x)), po)
  | VN_Goal(v)     -> (v, po)

and canonical_closure: type a. a closure -> pool -> a ex loc * pool =
  fun (clsptr,vs,ts) po ->
    let po = ref po in
    let vs = Array.map (fun p -> let (p, po') = canonical_valu true p !po in
                                 po := po'; p.elt) vs
    in
    let ts = Array.map (fun p -> let (p, po') = canonical true p !po in
                                 po := po'; p.elt) ts
    in
    (msubst (msubst clsptr vs) ts, !po)

and canonical_bndr_closure : type a b.(a,b) bndr_closure -> pool
                                  -> (a,b) bndr * pool =
  fun (funptr,vs,ts) po ->
    let po = ref po in
    let vs = Array.map (fun p -> let (p, po') = canonical_valu true p !po in
                                 po := po'; p.elt) vs
    in
    let ts = Array.map (fun p -> let (p, po') = canonical true p !po in
                                 po := po'; p.elt) ts
    in
    (msubst (msubst funptr vs) ts, !po)

and canonical : bool -> Ptr.t -> pool -> term * pool = fun clos p po ->
  match p with
  | Ptr.T_ptr p -> canonical_term clos p po
  | Ptr.V_ptr p -> let (v, po) = canonical_valu clos p po in
                   (Pos.none (Valu v), po)


and unif_cl
        : type a b.pool -> a sort -> (a,b) bndr_closure
                                  -> (a,b) bndr_closure -> pool =
  fun po s (f1,vs1,ts1) (f2,vs2,ts2 ) ->
    let po = ref po in
    if f1 == f2 then
      begin
        Array.iter2 (fun v1 v2 -> po := unif_vptr !po v1 v2) vs1 vs2;
        Array.iter2 (fun t1 t2 -> po := unif_ptr  !po t1 t2) ts1 ts2;
        !po
      end
    else
      raise NoUnif

(* NOTE: loose path shortening, not really a problem ? *)
and unif_vptr : pool -> VPtr.t -> VPtr.t -> pool = fun po p1 p2 ->
  unif_ptr po (Ptr.V_ptr p1) (Ptr.V_ptr p2)

(* NOTE: loose path shortening, not really a problem ? *)
and unif_tptr : pool -> TPtr.t -> TPtr.t -> pool = fun po p1 p2 ->
  unif_ptr po (Ptr.T_ptr p1) (Ptr.T_ptr p2)

and unif_ptr : pool -> Ptr.t -> Ptr.t -> pool = fun po p1 p2 ->
  let p1 = find p1 po in
  let p2 = find p2 po in
  log_edp2 "unif_ptr %a %a" Ptr.print p1 Ptr.print p2;
  if eq_ptr po p1 p2 then po else
  (* NOTE: could do [po = union p1 p2 po] but one should detect creation
     of cycle in the pool. remembering unification done or being done is
     simpler to avoid looping *)
  if test_uni p1 p2 po then raise NoUnif else
  let po = push_uni p1 p2 po in
  let po = match p1, p2 with
  | (Ptr.V_ptr vp1, Ptr.V_ptr vp2) ->
     let v1 = find_v_node vp1 po in
     let v2 = find_v_node vp2 po in
     unif_v_nodes po vp1 v1 vp2 v2
  | (Ptr.T_ptr tp1, Ptr.T_ptr tp2) ->
     let v1 = find_t_node tp1 po in
     let v2 = find_t_node tp2 po in
     unif_t_nodes po tp1 v1 tp2 v2
  | (Ptr.T_ptr p1, Ptr.V_ptr p2) ->
     let t1 = find_t_node p1 po in
     begin
       match t1 with
       | TN_UVar v ->
          let (p, po) = canonical_valu false p2 po in
          if uvar_occurs v p then raise NoUnif;
          uvar_set v (Pos.none (Valu p));
          join (Ptr.T_ptr p1) (Ptr.V_ptr p2) po
       | _ -> raise NoUnif
     end
  | (Ptr.V_ptr p1, Ptr.T_ptr p2) ->
     let t2 = find_t_node p2 po in
     begin
       match t2 with
       | TN_UVar v ->
          let (p, po) = canonical_valu false p1 po in
          if uvar_occurs v p then raise NoUnif;
          uvar_set v (Pos.none (Valu p));
          join (Ptr.T_ptr p2) (Ptr.V_ptr p1) po
       | _ -> raise NoUnif
     end
  in
  pop_uni p1 p2 po

and unif_expr : type a.pool -> a ex loc -> a ex loc -> pool =
  fun po e1 e2 ->
    log_edp2 "unif_expr %a %a" Print.ex e1 Print.ex e2;
    let po = ref po in
    if eq_expr ~oracle:(oracle po) ~strict:false e1 e2 then !po
    else raise NoUnif

and unif_bndr: type a b. pool -> a sort -> (a,b) bndr -> (a,b) bndr -> pool =
  fun po s e1 e2 ->
    log_edp2 "unif_bndr %a %a" Print.bndr e1 Print.bndr e2;
    let po = ref po in
    if eq_bndr ~oracle:(oracle po) ~strict:false s e1 e2 then !po
    else raise NoUnif

and unif_ho_appl : type a. pool -> a ho_appl -> a ho_appl -> pool =
  fun po a1 a2 ->
    let open Eq in
    let (HO(s1,(f1,vf1,tf1),(e1,ve1,te1)),
         HO(s2,(f2,vf2,tf2),(e2,ve2,te2))) = (a1, a2) in
    match eq_sort s1 s2 with
    | Eq ->
       if f1 == f2 && e1 == e2 then
         begin
           let po = Array.fold_left2 unif_vptr po vf1 vf2 in
           let po = Array.fold_left2 unif_ptr  po tf1 tf2 in
           let po = Array.fold_left2 unif_vptr po ve1 ve2 in
           let po = Array.fold_left2 unif_ptr  po te1 te2 in
           po
         end
       else raise NoUnif
    | NEq -> raise NoUnif

(** Equality functions on nodes. *)
and unif_v_nodes : pool -> VPtr.t -> v_node -> VPtr.t -> v_node -> pool =
  fun po p1 n1 p2 n2 ->
    log_edp2 "unif_v_nodes %a %a" print_v_node n1 print_v_node n2;
    if n1 == n2 then po else begin
    match (n1, n2) with
    | (VN_UVar({uvar_val = {contents = Set v}}), _) ->
       let po = reinsert (Ptr.V_ptr p1) po in
       unif_vptr po p1 p2
    | (_, VN_UVar({uvar_val = {contents = Set v}})) ->
       let po = reinsert (Ptr.V_ptr p2) po in
       unif_vptr po p1 p2
    | (VN_UVar(v1)   , VN_UVar(v2)   )
        when v1.uvar_key = v2.uvar_key -> assert false
    | (VN_UVar(v1)   , _             ) ->
       let (p, po) = canonical_valu false p2 po in
       if uvar_occurs v1 p then raise NoUnif;
       uvar_set v1 p;
       join (Ptr.V_ptr p1) (Ptr.V_ptr p2) po
    | (_             , VN_UVar(v2)   ) ->
       let (p, po) = canonical_valu false p1 po in
       if uvar_occurs v2 p then raise NoUnif;
       uvar_set v2 p;
       join (Ptr.V_ptr p2) (Ptr.V_ptr p1) po
    | _ ->
    match (n1, n2) with
    | (VN_LAbs(b1,l1), VN_LAbs(b2,l2)) ->
       if l1 <> l2 then raise NoUnif;
       unif_cl po V b1 b2
    | (VN_Cons(c1,p1), VN_Cons(c2,p2)) ->
       if c1.elt <> c2.elt then raise NoUnif;
       unif_vptr po p1 p2
    | (VN_Reco(m1)   , VN_Reco(m2)   ) ->
       if A.length m1 <> A.length m2 then raise NoUnif;
       A.fold2 unif_vptr po m1 m2
    | (VN_Scis       , VN_Scis       ) -> po
    | (VN_VWit(w1)   , VN_VWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (f1,a1,b1) = !(w1.valu) in
          let (f2,a2,b2) = !(w2.valu) in
          let po = unif_bndr po V f1 f2 in
          let po = unif_expr po a1 a2 in
          unif_expr po b1 b2)
    | (VN_UWit(w1)   , VN_UWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po V b1 b2)
    | (VN_EWit(w1)   , VN_EWit(w2)   ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po V b1 b2)
    | (VN_Vari(n1)   , VN_Vari(n2)   ) ->
       if eq_vars n1 n2 then po else raise NoUnif
    | (VN_HApp(e1)   , VN_HApp(e2)   ) ->
       unif_ho_appl po e1 e2
    | (VN_Goal(v1)   , VN_Goal(v2)   ) ->
       unif_expr po v1 v2
    | (_             , _             ) ->
       raise NoUnif
  end

and unif_t_nodes : pool -> TPtr.t -> t_node -> TPtr.t -> t_node -> pool =
  fun po p1 n1 p2 n2 -> if n1 == n2 then po else begin
    log_edp2 "unif_t_nodes %a %a" print_t_node n1 print_t_node n2;
    match (n1, n2) with
    | (TN_UVar({uvar_val = {contents = Set v}}), _) ->
       let po = reinsert (Ptr.T_ptr p1) po in
       unif_tptr po p1 p2
    | (_, TN_UVar({uvar_val = {contents = Set v}})) ->
       let po = reinsert (Ptr.T_ptr p2) po in
       unif_tptr po p1 p2
    | (TN_UVar(v1)   , TN_UVar(v2)   )
            when v1.uvar_key = v2.uvar_key -> assert false
    | (TN_UVar(v1)     , _               ) ->
       let (p, po) = canonical_term false p2 po in
       if uvar_occurs v1 p then raise NoUnif;
       uvar_set v1 p;
       join (Ptr.T_ptr p1) (Ptr.T_ptr p2) po
    | (_               , TN_UVar(v2)     ) ->
       let (p, po) = canonical_term false p1 po in
       if uvar_occurs v2 p then raise NoUnif;
       uvar_set v2 p;
       join (Ptr.T_ptr p2) (Ptr.T_ptr p1) po
    | _ ->
    match (n1, n2) with
    | (TN_Valu(p1)     , TN_Valu(p2)     ) ->
       unif_vptr po p1 p2
    | (TN_Appl(p11,p12,_), TN_Appl(p21,p22,_)) ->
       let po = unif_ptr po p11 p21 in
       unif_ptr po p12 p22
    | (TN_MAbs(b1)     , TN_MAbs(b2)     ) ->
       unif_cl po S b1 b2
    | (TN_Name(s1,p1)  , TN_Name(s2,p2)  ) ->
       let po = unif_expr po s1 s2 in
       unif_ptr po p1 p2
    | (TN_Delm(p1)     , TN_Delm(p2)     ) ->
       unif_ptr po p1 p2
    | (TN_Proj(p1,l1)  , TN_Proj(p2,l2)  ) ->
       if l1.elt <> l2.elt then raise NoUnif;
       unif_vptr po p1 p2
    | (TN_Case(p1,m1)  , TN_Case(p2,m2)  ) ->
       if A.length m1 <> A.length m2 then raise NoUnif;
       let po = unif_vptr po p1 p2 in
       A.fold2 (fun po -> unif_cl po V) po m1 m2
    | (TN_FixY(b1,_)   , TN_FixY(b2,_)   ) ->
       unif_cl po T b1 b2
    | (TN_Prnt(s1)     , TN_Prnt(s2)     ) ->
       if s1 <> s2 then raise NoUnif; po
    | (TN_UWit(w1)     , TN_UWit(w2)     ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po T b1 b2)
    | (TN_EWit(w1)     , TN_EWit(w2)     ) ->
       if !(w1.valu) == !(w2.valu) then po
       else if !(w1.vars) = [] && !(w2.vars) = [] then raise NoUnif
       else
         (let (_,t1,b1) = !(w1.valu) in
          let (_,t2,b2) = !(w2.valu) in
          let po = unif_expr po t1 t2 in
          unif_bndr po T b1 b2)
    | (TN_Vari(n1)     , TN_Vari(n2)     ) ->
       if not (eq_vars n1 n2) then raise NoUnif; po
    | (TN_HApp(e1)     , TN_HApp(e2)     ) ->
       unif_ho_appl po e1 e2
    | (TN_Goal(t1)     , TN_Goal(t2)     ) ->
       unif_expr po t1 t2
    | (_               , _               ) ->
       raise NoUnif
  end

and eq_val : pool ref -> valu -> valu -> bool = fun pool v1 v2 ->
  if v1.elt == v2.elt then true else
    begin
      let po = !pool in
      log_edp2 "eq_val: inserting %a = %a in context\n%a" Print.ex v1
           Print.ex v2 (print_pool "        ") po;
      let (p1, po) = add_valu true po v1 in
      let (p2, po) = add_valu true po v2 in
      log_edp2 "eq_val: insertion at %a and %a" VPtr.print p1 VPtr.print p2;
      log_edp2 "eq_val: obtained context:\n%a" (print_pool "        ") po;
      try pool := (UTimed.apply (unif_vptr po p1) p2); true
      with NoUnif -> false
    end

and eq_trm : pool ref -> term -> term -> bool = fun pool t1 t2 ->
  if t1.elt == t2.elt then true else
    begin
      let po = !pool in
      log_edp2 "eq_trm: inserting %a = %a in context\n%a" Print.ex t1
          Print.ex t2 (print_pool "        ") po;
      let (p1, po) = add_term true true po t1 in
      let (p2, po) = add_term true true po t2 in
      log_edp2 "eq_trm: insertion at %a and %a" Ptr.print p1 Ptr.print p2;
      log_edp2 "eq_trm: obtained context:\n%a" (print_pool "        ") po;
      try pool := (UTimed.apply (unif_ptr po p1) p2); true
      with NoUnif -> false
    end

and oracle pool = {
    default_oracle with
    eq_val = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_val pool v1) v2);
    eq_trm = (fun v1 v2 ->
      Chrono.add_time equiv_chrono (eq_trm pool v1) v2)
  }

let canonical_valu = canonical_valu false
let canonical_term = canonical_term false
let canonical      = canonical      false

(** Here starts the higher level function call from typing *)
type equiv   = term * term
type inequiv = term * term

(* Adds an inequivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. It returns a
  boolean to know if the inequation was already known. *)
let add_inequiv : inequiv -> pool -> bool * pool = fun (t,u) pool ->
  log_edp2 "add_inequiv: inserting %a ≠ %a in context\n%a" Print.ex t
    Print.ex u (print_pool "        ") pool;
  if eq_expr t u then
    begin
      log_edp2 "immediate contradiction";
      bottom ()
    end;
  let (pt, pool) = add_term true true pool t in
  let (pu, pool) = add_term true true pool u in
  log_edp2 "add_inequiv: insertion at %a and %a" Ptr.print pt Ptr.print pu;
  log_edp2 "add_inequiv: obtained context:\n%a" (print_pool "        ") pool;
  try
    ignore (UTimed.apply (unif_ptr pool pt) pu);
    log_edp2 "add_inequiv: contradiction found";
    bottom ()
  with NoUnif ->
    let fn (pr,ps) = (eq_ptr pool pt pr && eq_ptr pool pu ps)
                     || (eq_ptr pool pt ps && eq_ptr pool pu pr)
    in
    let known = List.exists fn pool.ineq in
    let pool = if known then pool else {pool with ineq=(pt,pu)::pool.ineq} in
    (known, pool)

(* Main module interface. *)

(* Adds an equivalence to a context, producing a bigger context. The
   exception [Contradiction] is raised when expected. It returns a
  boolean to know if the equation was already known. *)
let add_equiv : equiv -> pool -> bool * pool = fun (t,u) pool ->
  log_edp2 "add_equiv: inserting %a = %a in context\n%a" Print.ex t
    Print.ex u (print_pool "        ") pool;
  if eq_expr t u then
    begin
      log_edp2 "add_equiv: trivial proof";
      (true, pool)
    end
  else
  let (pt, pool) = add_term true true pool t in
  let (pu, pool) = add_term true true pool u in
  let known = eq_ptr pool pt pu in
  log_edp2 "add_equiv: insertion at %a and %a" Ptr.print pt Ptr.print pu;
  log_edp2 "add_equiv: obtained context (1):\n%a"
    (print_pool "        ") pool;
  let pool = union pt pu pool in
  log_edp2 "add_equiv: obtained context (2):\n%a"
    (print_pool "        ") pool;
  (known, pool)

(** Add the hypothesis that a vptr is nobox, It returns a boolean to know if the
   fact was already known.  *)
let add_vptr_nobox : VPtr.t -> pool -> bool * pool = fun vp po ->
  let vp = find_valu vp po in
  if not (get_bs vp po) then
    begin
      let po = set_bs vp po in
      let po = mk_eq_delim (V_ptr vp) po in
      let nps = parents (Ptr.V_ptr vp) po in
      let po = MapKey.fold (fun k l po ->
                   if is_head k then PtrSet.fold reinsert l po else po) nps po
      in
      (false, po)
    end
  else (true, po)

(** Add the hypothesis that a value is nobox, It returns a boolean to know if the
   fact was already known.  *)
let add_nobox : valu -> pool -> bool * pool = fun v po ->
  log_edp2 "add_nobox: inserting %a not box in context\n%a" Print.ex v
    (print_pool "        ") po;
  let (vp, po1) = add_valu true po v in
  let (known,po1) = add_vptr_nobox vp po1 in
  let po = if known then po else po1 in
  (known, po)

(** [proj_eps v l] denotes a value “w” such that “v.l ≡ w”. *)
let proj_eps : Bindlib.ctxt -> valu -> string -> valu * Bindlib.ctxt =
  fun names v l ->
    let w =
      let name = proj_name l in
      let x = new_var (mk_free V) name in
      let term_x = valu no_pos (vari no_pos x) in
      let v_dot_l = proj no_pos (box v) (Pos.none l) in
      let w = rest no_pos unit_prod (equiv term_x true v_dot_l) in
      unbox (bind_var x w)
    in
    let t = Pos.none (Valu(Pos.none (Reco A.empty))) in
    ewit names V t (no_pos, w)

let find_proj : pool -> Bindlib.ctxt -> valu -> string
                -> valu * pool * Bindlib.ctxt =
  fun po names v l ->
    try
      let (vp, po) = add_valu true po v in
      let vp = find_valu vp po in
      let n = find_v_node vp po in
      let (wp, w, po, names) =
        match n with
        | VN_Reco(m) ->
           let pt = A.find l m in
           (pt, Pos.none (VPtr pt), po, names)
        | _ ->
           let (w,names) = proj_eps names v l in
           let (wp,po) = add_valu true po w in
           let t = Pos.none (Proj(v,Pos.none l)) in
           let (pt,po) = add_term true false po t in
           let po = union (Ptr.V_ptr wp) pt po in
           (wp, w, po, names)
      in
      let (_, po) = add_vptr_nobox wp po in
      (w, po, names)
    with Contradiction as e -> raise e
       | e -> bug_msg "unexpected exception in find_proj: %s"
                      (Printexc.to_string e);
              assert false


(* NOTE: sum with one case should not fail, and be treated as projection *)
let find_sum : pool -> valu -> (string * valu * pool) option = fun po v ->
  try
    let (vp, po) = add_valu false po v in
    let vp = find_valu vp po in
    let n = find_v_node vp po in
    match n with
    | VN_Cons(c,pt) ->
       Some (c.elt, Pos.none (VPtr pt), po)
    | _ -> raise Not_found
  with Not_found -> None

(* Adds no box to the bool *)
let check_nobox : valu -> pool -> bool * pool = fun v pool ->
  log_edp2 "inserting %a not box in context\n%a" Print.ex v
    (print_pool "        ") pool;
  let (vp, pool) = add_valu true pool v in
  let vp = find_valu vp pool in
  (get_bs vp pool, pool)

(** [is_nobox t returns Some(v,is_nobox) with v = t it t is a value
    and is_nobox is true if v is syntactically not box *)
let is_nobox_value : term -> (valu * bool) option = fun t ->
  let rec fn v = match (Norm.whnf v).elt with
    | LAbs _    -> true
    | Cons(_,v) -> fn v
    | Reco(l)   -> A.for_all (fun _ (_,v) -> fn v) l
    | Scis      -> true
    | HDef(_,d) -> fn d.expr_def
    | _         -> false
  in
  let rec gn t =
    match (Norm.whnf t).elt with
    | Valu v -> Some(v,fn v)
    | Hint(_,t) -> gn t
    | HDef(_,d) -> gn d.expr_def
    | _      -> None
  in
  gn t

(* Test whether a term is equivalent to a value or not. *)
let is_value : term -> pool -> bool * bool * pool = fun t pool ->
  log_edp2 "inserting %a not box in context\n%a" Print.ex t
    (print_pool "        ") pool;
  match is_nobox_value t with
  | Some(_,nb) -> (true, nb, pool)
  | _ ->
  let (pt, pool) = add_term true true pool t in
  log_edp2 "insertion at %a" Ptr.print pt;
  log_edp2 "obtained context:\n%a" (print_pool "        ") pool;
  let no_box = is_nobox pt pool in
  let is_val = match pt with
    | Ptr.V_ptr(v) -> true
    | Ptr.T_ptr(_) -> false
  in
  log_edp1 "%a is%s a value and is%s box" Print.ex t
      (if is_val then "" else " not")
      (if no_box then " not" else "");
  (is_val, no_box, pool)

(* Test whether a term is equivalent to a value or not. *)
let to_value : term -> pool -> valu option * pool = fun t pool ->
  match is_nobox_value t with
  | Some(v,_) -> (Some v, pool)
  | _ ->
  let (pt, pool) = add_term true true pool t in
  match pt with
  | Ptr.V_ptr(v) -> Some (Pos.none (VPtr v)), pool
  | Ptr.T_ptr(_) -> None, pool

(** learn a relation (equation, inequation or nobox) and returns a boolean
   telling if the fact was already known *)
let learn : pool -> rel -> bool * pool = fun pool rel ->
  log_edp1 "learning %a" Print.rel rel;
  try
    let ctx =
      match rel with
      | Equiv(t,b,u) ->
         (if b then add_equiv else add_inequiv) (t,u) pool
      | NoBox(v) ->
         add_nobox v pool
    in
    log_edp1 "learned  %a" Print.rel rel; ctx
  with Contradiction ->
    log_edp1 "contradiction in the context";
    raise Contradiction

(** type of blocked evaluations sent back to typing for automatic
    case analysis and totality in auto_prove *)
type blocked =
  | BTot of Ptr.t * term
  | BCas of Ptr.t * term * A.key list

let eq_blocked : blocked -> blocked -> bool =
  fun b1 b2 ->
    match (b1, b2) with
    | (BTot(pt,e)  , BTot(pu,f)  ) -> Ptr.compare pt pu = 0 || eq_expr e f
    | (BCas(pt,e,_), BCas(pu,f,_)) -> Ptr.compare pt pu = 0 || eq_expr e f
    | (_           , _           ) -> false

let eq_ptr_blocked : Ptr.t -> blocked -> bool =
  fun pt b2 ->
    match b2 with
    | BTot(pu,_)   -> Ptr.compare pt pu = 0
    | BCas(pu,_,_) -> Ptr.compare pt pu = 0

(** the exception when failing to prove carry the blocked evaluations *)
exception Failed_to_prove of rel * blocked list
let equiv_error : rel -> blocked list -> 'a =
  fun rel bls -> raise (Failed_to_prove(rel, bls))

let cmp_orig (p,x) (q,y) = match (x.elt, y.elt) with
    | (_               , Valu{elt=VPtr _}) -> -1
    | (Valu{elt=VPtr _},  _              ) ->  1
    | (Valu{elt=VDef _}, _               ) -> -1
    | ( _              , Valu{elt=VDef _}) ->  1
    (*    | (Valu{elt=VWit _}, Valu{elt=VWit _}) ->  compare p q*)
    | (Valu{elt=VWit _}, _               ) -> -1
    | (_               , Valu{elt=VWit _}) ->  1
    | (Proj _          , _               ) -> -1
    | (_               , Proj _          ) ->  1
    | (_               , _               ) ->  0

(* Search a vwit or a projection equal to a given term in the pool *)
let term_vwit : term -> pool -> term = fun t po ->
  (*Printf.eprintf "term_vwit: %a\n%!" Print.ex t;*)
  let (pt, po) = add_term true true po t in
  let fn (p,t) = eq_ptr po p pt in
  let l = List.find_all fn po.os in
  if l = [] then raise Not_found;
  snd (List.hd (List.sort cmp_orig l))

(* Search a vwit or a projection equal to a given term in the pool *)
let valu_vwit : valu -> pool -> valu = fun t po ->
  (*Printf.eprintf "valu_vwit: %a\n%!" Print.ex t;*)
  let (pt, po) = add_valu true po t in
  let fn (p,t) =
    eq_ptr po p (Ptr.V_ptr pt) &&
      (match (Norm.repr t).elt with Valu _ -> true
                                  | _      -> false)
  in
  let l = List.find_all fn po.os in
  if l = [] then raise Not_found;
  let t = snd (List.hd (List.sort cmp_orig l)) in
  match (Norm.repr t).elt with
  | Valu v -> v
  | _      -> assert false


(** test is a node is a nobox value *)
let test_value : Ptr.t -> pool -> bool = fun p po ->
  let p = find p po in
  match p with
    | Ptr.V_ptr(v) -> is_nobox p po
    | Ptr.T_ptr(_) -> false

(** Try to get the list of cases from the type in a VWit to limit
    the cases in auto *)
let get_cases : Ptr.v_ptr -> pool -> A.key list option = fun pv po ->
  let is_vwit = function VN_VWit _ -> true | _ -> false in
  let l = List.find_all (fun (v',nn) ->
              eq_ptr po (Ptr.V_ptr v') (Ptr.V_ptr pv)
              && is_vwit nn) po.vs in
  let rec gn = function
    | []                   -> None
    | (_, VN_VWit(e)) :: l ->
       let (_,a,_) = !(e.valu) in
       let rec fn a =
         match (Norm.whnf a).elt with
         | HDef(_,d) -> fn d.expr_def
         | DSum(s)   -> Some(A.keys s)
         | FixM(s,_,b,l) -> fn (apply_args (bndr_term b) l)
         | FixN(s,_,b,l) -> fn (apply_args (bndr_term b) l)
         | Memb(_,a) -> fn a
         | Rest(a,_) -> fn a
         | Impl(_,a) -> fn a
         | Univ(s,b) -> fn (bndr_term b)
         | Exis(s,b) -> fn (bndr_term b)
         | _         -> gn l
       in
       fn a
    | _ -> assert false
  in gn l

(** get one original term from the pool or their applications. *)
let get_orig : Ptr.t -> pool -> term =
  fun p po ->
    let rec fn p =
      try
        let l = List.find_all (fun (v',e) -> eq_ptr po p v') po.os in
        if l = [] then raise Not_found;
        snd (List.hd (List.sort cmp_orig l))
      with Not_found ->
        let is_appl = function TN_Appl _ | TN_Proj _ -> true | _ -> false in
        let (v',nn) = List.find (fun (v',nn) ->
                          eq_ptr po (Ptr.T_ptr v') p && is_appl nn) po.ts
        in
        match nn with
        | TN_Appl(u1,u2,l) ->
           let u1 = fn u1 in
           let u2 = fn u2 in
           Pos.none (Appl(u1, u2,l))
        | TN_Proj(u1,l) ->
           x_proj no_pos (fn (Ptr.V_ptr u1)) l
        | _ -> assert false
    in
    let t = fn p in
    let open Mapper in
    let mapper : type a. recall -> a ex loc -> a ebox = fun r t ->
      match t.elt with
      | UWit _ | EWit _ ->
         begin
           match sort t with
           | (T, t) -> r.recall (term_vwit t po)
           | _      -> r.default t
         end
      | VPtr _ ->
         begin
           match sort t with
           | (V, t) -> r.recall (valu_vwit t po)
           | _      -> .
         end
      | Valu(v) ->
         begin
           match (Norm.whnf v).elt with
           | UWit _ | EWit _ | VPtr _ -> r.recall (term_vwit t po)
           | _ -> r.default t
         end
      | _      -> r.default t
    in
    let t0 = unbox (map ~mapper:{mapper} t) in
    (*Printf.eprintf "%a ==> %a\n%!" Print.ex t Print.ex t0;*)
    t0

let is_let_underscore e = match e.elt with
  | Appl({elt = Valu({elt = LAbs(_,b,NoLz)})},_,NoLz)
        -> binder_constant (snd b)
  | _   -> false

(** get all blocked terms in the pool *)
let get_blocked : pool -> blocked list -> blocked list = fun po old ->
  (*Printf.eprintf "obtained context:\n%a\n\n" (print_pool "        ") po;*)
  (*Printf.eprintf "coucou 0 %d\n%!" (List.length !adone);*)
  let bl =
    List.fold_left (fun (acc:blocked list) (tp,tn) ->
      let u = Ptr.T_ptr tp in
      if List.exists (eq_ptr_blocked u) old then acc else
      (*Printf.eprintf "testing %a %a %b %b\n%!" TPtr.print tp print_t_node tn
                     (get_ns tp po) (get_fs tp po);*)
      if not (get_ns tp po) && is_free u po then
      begin
        try
          match tn with
          | TN_Appl(_,v,l) when not (test_value v po) ->
             begin
               try
                 let e = get_orig v po in
                 (* no need to prove totality of let _ = t; u *)
                 if is_let_underscore e then raise Not_found;
                 let b = BTot(u,e) in
                 if List.exists (eq_blocked b) acc
                    || List.exists (eq_blocked b) old then acc
                 else
                   begin
                     log_aut "blocked arg %a" Print.ex e;
                     b :: acc
                   end
               with Not_found -> acc
             end
          | TN_Case(v,b) ->
             let cases = List.map fst (A.bindings b) in
             let cases = match get_cases v po with
               | Some l -> List.filter (fun x -> List.mem x l) cases
               | None   -> cases
             in
             let e = get_orig (Ptr.V_ptr v) po in
             let b = BCas (u, e, cases) in
             if List.exists (eq_blocked b) acc
                || List.exists (eq_blocked b) old then acc
             else
               begin
                 log_aut "blocked case %a %t" Print.ex e
                     (fun ch -> List.iter (Printf.fprintf ch "%s ") cases);
                 b :: acc
               end
          | _ -> acc
        with Not_found -> acc
      end else acc
    ) [] po.ts
  in
  let bl =
    List.fold_left (fun acc (vp, vn) ->
        let u = Ptr.V_ptr vp in
        if not (is_nobox u po) then
          match vn with
          | VN_VWit(e) ->
             let (_,a,_) = !(e.valu) in
             let rec fn acc a =
               match  a.elt with
               | Memb(t,a) ->
                  let b = BTot(u,t) in
                  let acc =
                    if List.exists (eq_blocked b) acc then acc else
                      begin
                        log_aut "blocked arg vwit %a" Print.ex t;
                        b :: acc
                      end
                  in
                  fn acc a
               | _ -> acc
             in
             fn acc a
          | _ -> acc
        else acc
      ) bl po.vs
  in
  bl

 let prove : pool -> blocked list -> rel -> unit = fun pool old rel ->
  log_edp1 "proving  %a" Print.rel rel;
  try
    let st = UTimed.Time.save () in
    let pool = match rel with
      | Equiv(t,b,u) ->
         snd ((if b then add_inequiv else add_equiv) (t,u) pool)
      | NoBox(v) ->
         let (b, pool) = check_nobox v pool in
         if b then raise Contradiction;
         pool
    in
    UTimed.Time.rollback st;
    let bls = get_blocked pool old in
    log_edp1 "failed to prove %a" Print.rel rel;
    equiv_error rel bls
  with Contradiction -> log_edp1 "proved   %a" Print.rel rel


let unif_expr : type a. pool -> a ex loc -> a ex loc -> bool =
  fun po a b ->
    eq_expr ~oracle:(oracle (ref po)) ~strict:false a b

let unif_bndr
    : type a b. pool -> a sort -> (a, b) bndr -> (a, b) bndr -> bool
  = fun po s a b ->
    eq_bndr ~oracle:(oracle (ref po)) ~strict:false s a b

let leq_expr : pool -> (ordi * ordi) list -> p ex loc -> p ex loc -> bool =
  fun po pos a b ->
    eq_expr ~oracle:{(oracle (ref po)) with leq_ord = Ordinal.leq_ordi pos} ~strict:false a b


let learn pool rel    = Chrono.add_time equiv_chrono (learn pool) rel
let prove pool rel    = Chrono.add_time equiv_chrono (prove pool) rel
let to_value t eqs    = Chrono.add_time equiv_chrono (to_value t) eqs
let is_value t eqs    = Chrono.add_time equiv_chrono (is_value t) eqs
let check_nobox v eqs = Chrono.add_time equiv_chrono (check_nobox v) eqs
let add_nobox v eqs   = Chrono.add_time equiv_chrono (add_nobox v) eqs
let find_proj eqs v   = Chrono.add_time equiv_chrono (find_proj eqs) v
let find_sum eqs v    = Chrono.add_time equiv_chrono (find_sum eqs) v
