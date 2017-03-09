
type rec nat = [ Z ; S of nat ]

val zero : nat = Z[]
val succ : nat ⇒ nat = fun n → S[n]

val rec add : nat ⇒ nat ⇒ nat = fun n m →
  case n of
  | Z[] → m
  | S[p] → succ (add p m)

val rec add_total : ∀n m∈nat, ∃v:ι, add n m ≡ v = fun n m →
  case n of
  | Z[] → {}
  | S[p] → let ind_hyp = add_total p m in {}

type rec list<a:ο> = [ Nil; Cns of { hd : a; tl : list }  ]

val nil : ∀a:ο, list<a> = Nil[]
val cns : ∀a:ο, a ⇒ list<a> ⇒ list<a> =
  fun e l → Cns[{ hd = e; tl = l }]

val rec length : ∀a:ο, list<a> ⇒ nat = fun l →
  case l of
  | Nil[] → zero
  | Cns[c] → succ (length c.tl)

val rec length_total : ∀a:ο, ∀l∈list<a>, ∃v:ι, v ≡ length l = fun l →
  case l of
  | Nil[] → {}
  | Cns[c] → let ind = length_total c.tl in {}

type vec<a:ο,s:τ> = ∃l:ι, l∈(list<a> | length l ≡ s)
// The fact that s:τ is very important
// The position of the partenthesis is important

val vnil : ∀a:ο, vec<a,zero> = nil

val vcns : ∀a:ο,∀s:ι, ∀x∈a, vec<a,s> ⇒ vec<a,succ s> =
   fun y ls → Cns[{hd= y;tl= ls}]

val rec app : ∀a:ο, ∀n1 n2:ι, vec<a,n1> ⇒ vec<a,n2> ⇒ vec<a,add n1 n2> =
  Λa:ο. fun l1 l2 →
  case l1 of
  | Nil[] → l2
  | Cns[c] →
      let lem = length_total c.tl in
      (case length l1 of
      | Z[] → ✂
      | S[p1] →
        let r = app c.tl l2 in
        let lem = length_total (r : list<a>) in
        vcns c.hd r)

val app3 : ∀a:ο, ∀n1 n2 n3:ι,
           vec<a,n1> ⇒ vec<a,n2> ⇒ vec<a,n3> ⇒ vec<a,add n1 (add n2 n3)> =
    fun l1 l2 l3 →
      let lem = add_total (length l2) (length l3) in
      app l1 (app l2 l3)