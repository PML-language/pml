open Ast
open Compare
open Uvars
open Sorts
open Pos
open Bindlib

let owmu_counter = ref (-1)
let ownu_counter = ref (-1)
let osch_counter = ref (-1)

module VWitHash = Hashtbl.Make(VWit)
let vwit_hash   = VWitHash.create 256

module QWitHash = Hashtbl.Make(QWit)
type aqwit = Q : ('a qwit, string) eps -> aqwit
let qwit_hash   = QWitHash.create 256

module OWitHash = Hashtbl.Make(OWit)
let owit_hash   = OWitHash.create 256

module SWitHash = Hashtbl.Make(SWit)
let swit_hash   = SWitHash.create 256

module CWitHash = Hashtbl.Make(CWit)
let cwit_hash   = CWitHash.create 256

let reset_epsilons () =
  VWitHash.clear vwit_hash;
  QWitHash.clear qwit_hash;
  OWitHash.clear owit_hash;
  SWitHash.clear swit_hash;
  CWitHash.clear cwit_hash

let vwit : ctxt -> (v,t) bndr -> prop -> prop -> (vwit, string) eps * ctxt =
  fun ctx f a b ->
    let valu = (f,a,b) in
    try (VWitHash.find vwit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            Timed.(w.vars := VWit.vars valu);
            Timed.(w.hash := VWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = VWitHash.find vwit_hash valu in
              (*Printf.eprintf "merge vwit\n%!";*)
              Timed.(w.valu := !(w'.valu))
            with Not_found ->
              VWitHash.add vwit_hash valu w
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name f).elt in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu}
      in
      refr ~force:true w;
      (w, ctx)

let vwit : ctxt -> (v,t) bndr -> prop -> prop -> valu * ctxt =
  fun ctx f a b ->
    let (eps, ctx) = vwit ctx f a b in
    (Pos.none (VWit eps), ctx)

let qwit : type a. ctxt -> a sort -> term -> (a,p) bndr
                -> (a qwit, string) eps * ctxt =
  fun ctx s t b ->
    let valu = (s,t,b) in
    let key = QWit.Q(valu) in
    try
      let Q(w) = QWitHash.find qwit_hash key in
      let (s',_,_) = !(w.valu) in
      match eq_sort s s' with
      | Eq.Eq -> (w, ctx)
      | _ -> assert false
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            Timed.(w.vars := QWit.vars key);
            Timed.(w.hash := QWit.hash key);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let Q(w') = QWitHash.find qwit_hash key in
              (*Printf.eprintf "merge qwit\n%!";*)
              let (s',_,_) = !(w'.valu) in
              match eq_sort s s' with
              | Eq.Eq -> Timed.(w.valu := Obj.magic !(w'.valu))
              | _ -> assert false
            with Not_found ->
              QWitHash.add qwit_hash key (Q w)
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu}
      in
      refr ~force:true w;
      (w, ctx)

let uwit : type a. ctxt -> a sort -> term -> (a,p) bndr -> a ex loc * ctxt =
  fun ctx s t f ->
    let (eps, ctx) = qwit ctx s t f in
    (Pos.none (UWit eps), ctx)

let ewit : type a. ctxt -> a sort -> term -> (a,p) bndr -> a ex loc * ctxt =
  fun ctx s t f ->
    let (eps, ctx) = qwit ctx s t f in
    (Pos.none (EWit eps), ctx)

let owit : ctxt -> ordi -> term -> (o,p) bndr -> (owit, string) eps * ctxt =
  fun ctx o a b ->
    let valu = (o,a,b) in
    try (OWitHash.find owit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            Timed.(w.vars := OWit.vars valu);
            Timed.(w.hash := OWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = OWitHash.find owit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              Timed.(w.valu := !(w'.valu))
            with Not_found ->
              OWitHash.add owit_hash valu w
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu}
      in
      refr ~force:true w;
      (w, ctx)

let owmu : ctxt -> ordi -> term -> (o, p) bndr -> ordi * ctxt =
  fun ctx o t b ->
    let (eps, ctx) = owit ctx o t b in
    (Pos.none (OWMu eps), ctx)

let ownu : ctxt -> ordi -> term -> (o, p) bndr -> ordi * ctxt =
  fun ctx o t b ->
    let (eps, ctx) = owit ctx o t b in
    (Pos.none (OWNu eps), ctx)

let swit : ctxt -> (s,t) bndr -> prop -> (swit, string) eps * ctxt =
  fun ctx b s ->
    let valu = (b,s) in
    try (SWitHash.find swit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            Timed.(w.vars := SWit.vars valu);
            Timed.(w.hash := SWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = SWitHash.find swit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              Timed.(w.valu := !(w'.valu))
            with Not_found ->
              SWitHash.add swit_hash valu w
          end
      in
      let v, ctx = new_var_in ctx (mk_free V) (bndr_name b).elt in
      let rec w = { vars = ref []
                  ; name = name_of v
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu}
      in
      refr ~force:true w;
      (w, ctx)

let swit : ctxt -> (s,t) bndr -> prop -> stac * ctxt =
  fun ctx f a ->
    let (eps, ctx) = swit ctx f a in
    (Pos.none (SWit eps), ctx)

let cwit : ctxt -> schema -> (schema, string array) eps * ctxt =
  fun ctx valu ->
    try (CWitHash.find cwit_hash valu, ctx)
    with Not_found ->
      let rec refr ?(force=false) w =
        if force || exists_set !(w.vars) then
          begin
            let oldvars = !(w.vars) in
            Timed.(w.vars := CWit.vars valu);
            Timed.(w.hash := CWit.hash valu);
            List.iter (fun (U(_,v)) ->
                let same (U(_,w)) = v.uvar_key = w.uvar_key in
                if not (List.exists same oldvars)
                then uvar_hook v (fun () -> refr w)) !(w.vars);
            try
              let w' = CWitHash.find cwit_hash valu in
              (*Printf.eprintf "merge owit\n%!";*)
              Timed.(w.valu := !(w'.valu))
            with Not_found ->
              CWitHash.add cwit_hash valu w
          end
      in
      let names = match valu with
        | FixSch s -> mbinder_names (snd s.fsch_judge)
        | SubSch s -> mbinder_names s.ssch_judge
      in
      let v, ctx = new_mvar_in ctx (mk_free V) names in
      let rec w = { vars = ref []
                  ; name = names
                  ; hash = ref 0
                  ; refr = (fun () -> refr w)
                  ; valu = ref valu}
      in
      refr ~force:true w;
      (w, ctx)

let osch : int -> ordi option -> (schema, string array) eps -> ordi =
  fun i o eps -> Pos.none (OSch(i, o, eps))
