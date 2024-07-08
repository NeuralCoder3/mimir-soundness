From stdpp Require Import base relations.
From iris Require Import prelude.
From thorin.lib Require Import maps.
From thorin Require Import lang notation.
Require Import Coq.Program.Equality.
(* From Autosubst Require Export Autosubst. *)

(*
  Usually, typing uses deBrujin indices for naming
  this makes freshness, no-clash easy

  Our case is special in multiple ways:
  - types and expressions are the same
  - evaluation also happens in types
  - we have multiple kind levels (the type of types has a type (at which level we get impredicative))
  - our typing is mutual recursive with an assignability relation
  - we have nested inductive predicates

  Autosubst has support for De Bruijn indices and their substitution
  Usually, the typing is annotated with the type level in the presence of indices
  and lifting lemmas are defined
*)

Definition typing_context := gmap string expr.
Implicit Types
  (Γ : typing_context)
  (e : expr).

(* Inductive kind_dominance: list expr -> expr -> Prop :=
  | empty_dom: kind_dominance [] Star
  | star_idem xs s':
      kind_dominance xs s' →
      kind_dominance (Star::xs) s'
  | box_dom xs s':
      kind_dominance xs s' →
      kind_dominance (Box::xs) Box *)
(* where "[ s1 s2 .. sn ] ⇝ s" := (kind_dominance [s1; s2; ..; sn] s). *)
(* . *)


(* TODO: check with page 46 in https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf *)

(* TODO: kind vs sort *)
(* Definition sort s := s = Star \/ s = Box. *)

Require Import Coq.Program.Wf.

(*
e, n, Ts: binder*expr

Tj' = Tj[e#0_n/x0]...[e#(j-1)_n/x_(j-1)] (j < n)
=> [
  T0,
  subst x0 (Extract e (LitIdx n i)) T1,
  ...

Note: we use Function instead of Program Fixpoint for the _equation lemma
*)
Fixpoint close_subst_aux (e:expr) (n:nat) (Ts: list ((binder*expr)*Fin.t n)) 
  : list expr :=
  match Ts with
  | [] => []
  | ((x,T),idx)::Tr => 
    T :: 
    let Tr' := close_subst_aux e n Tr in 
    (* now with rest substituted in, lastly subst our term *)
    map (subst' x (Extract e (LitIdx n idx))) Tr'
    (* let Tr' :=  *)
    (* close_subst e n 
      (map (fun '((b_j,T_j),idx_j) => ((b_j,subst' x (Extract e (LitIdx n idx)) T_j),idx_j)) Ts') *)
  end.

Definition close_subst e n Ts :=
  let (idxs,_) := fin_list n in
  close_subst_aux e n (combine Ts idxs).

Definition extracts n e :=
  let (idxs, _) := fin_list n in
  map (fun idx => Extract e (LitIdx n idx)) idxs
  .

Definition Star := Sort 0.
Definition insert_name (x: binder) (e: expr) (Γ: typing_context) :=
  match x with
  | BNamed x => <[x := e]> Γ
  | BAnon => Γ
  end.

Reserved Notation "'TY' Γ ⊢ e : A" (at level 74, e, A at next level).
Reserved Notation "'TY' Γ ⊢ A ← e" (at level 74, e, A at next level).
Inductive syn_typed : typing_context → expr → expr → Prop :=
   | typed_sort Γ n:
      TY Γ ⊢ Sort n : Sort (S n)
   | typed_bot Γ:
      TY Γ ⊢ Bot : Star
   | typed_nat Γ:
      TY Γ ⊢ Nat : Star
   | typed_idx Γ:
      TY Γ ⊢ Idx : (Pi BAnon Nat Star)
   | typed_lit_nat Γ n:
      TY Γ ⊢ (#n)%E : Nat
    | typed_lit_idx Γ n i:
      (* i < n by construction i:fin n *)
      TY Γ ⊢ (LitIdx n i) : (App Idx n)
    | typed_var Γ x A :
      Γ !! x = Some A →
      (* TODO: missing in paper: A has to be typed (with a kind) *)
      (* we check types at binder position, otherwise endless loop *)
      (* TY Γ ⊢ A : sA → *)
      TY Γ ⊢ (Var x) : A
    (* no axiom typing *)
    | typed_pi Γ T sT x U sU:
      TY Γ ⊢ T : Sort sT →
      (* TY (<[x := T]> Γ) ⊢ U : sU → *)
      TY (insert_name x T Γ) ⊢ U : Sort sU →
      (* kind_dominance [sT; sU] s → *)
      TY Γ ⊢ (Pi x T U) : (max sT sU)
    (* | typed_pi_anon Γ T sT U sU s:
      (* same as above but ignore unnamed binder *)
      TY Γ ⊢ T : sT →
      TY Γ ⊢ U : sU →
      (* kind_dominance [sT; sU] s → *)
      TY Γ ⊢ (Pi BAnon T U) : (max sT sU) *)
    | typed_lam Γ x T ef U e s:
      (* TODO: typing of T and U (not in paper) (star as well as box allowed) 

      (well we might want to allow app, ... => any valid type
      this allows λ (x:5) : Nat, 42
      which can never be applied
      but it should not destroy anything)
      
        e.g. 
        U = Nat : *
        λ (x:Nat) : Nat, 5

        U = * : Box
        λ (x:Nat) : *, Nat
      *)
      (* TY Γ ⊢ T : sT →
      TY (insert_name x T Γ) ⊢ U : sU → *)
      TY Γ ⊢ (Pi x T U) : s →
      TY (insert_name x T Γ) ⊢ ef : Bool →
      (* TY (<[x := T]> Γ) ⊢ U ← e → *)
      type_assignable (insert_name x T Γ) U e →
      (* without tuples, assignable becomes typed *)
      (* TY (insert_name x T Γ) ⊢ e : U → *)
      TY Γ ⊢ (Lam x T ef U e) : (Pi x T U)
    (* | typed_lam_anon Γ T ef U e sT sU:
      TY Γ ⊢ T : sT →
      TY Γ ⊢ U : sU →
      TY Γ ⊢ ef : Bool →
      (* ignore x *)
      type_assignable Γ U e →
      TY Γ ⊢ (Lam BAnon T ef U e) : (Pi BAnon T U) *)
    | typed_app Γ e eT x T U U':
      (* handles both named and unnamed *)
      TY Γ ⊢ e : (Pi x T U) →
      type_assignable Γ T eT →
      (* without tuples, assignable becomes typed *)
      (* TY Γ ⊢ eT : T → *)
      normal_eval (subst' x eT U) U' →
      TY Γ ⊢ (App e eT) : U'
    (*
      all typed under the previous
      and dominating kind overall
      we unroll directly instead of a mutual predicate
      we use the associativity of dominance for the formulation 
      of pairwise domainance
    *)
    (* TODO: mistake in pdf (n-2 in assumption) *)
    (* | typed_sigma_empty Γ:
      TY Γ ⊢ Sigma [] : Star
    | typed_sigma_cons Γ x T s xs s' :
      TY Γ ⊢ T : Sort s →
      TY (insert_name x T Γ) ⊢ Sigma xs : Sort s' →
      (* kind_dominance [s; s'] s'' → *)
      TY Γ ⊢ (Sigma ((x, T)::xs)) : Sort (max s s')
    (* | typed_sigma_cons_anon Γ T s xs s' s'':
      TY Γ ⊢ T : s →
      TY Γ ⊢ Sigma xs : s' →
      kind_dominance [s; s'] s'' →
      TY Γ ⊢ (Sigma ((BAnon, T)::xs)) : s'' *)
    | typed_tuple Γ es Ts T:
      Forall2 (syn_typed Γ) es Ts →
      (* 
      TODO: how to handle [bool, fun x -> if x then 1 else 0] : [T:*, T -> Nat] 
      
      alternative: name each fresh, typed under previous names
      *)
      (* T = Sigma (map (fun T => (BAnon, T)) Ts) -> *)
      normal_eval (Sigma (map (fun T => (BAnon, T)) Ts)) T →
      TY Γ ⊢ (Tuple es) : T
    | typed_arr Γ x en T s:
      (* TODO: mistake in pdf (s vs s') *)
      (* TODO: s should be a kind (it is not restricted in Pdf) => why does it need to be a kind? Why can't we have <<x:5;5>> with s = Nat *)
      (* sort s → *)
      TY Γ ⊢ en : Nat →
      (* TY (<[x := App Idx en]> Γ) ⊢ T : s → *)
      (* TY (insert_name x (App Idx en) Γ) ⊢ T : s → *)
      TY (insert_name x (App Idx en) Γ) ⊢ T : Sort s →
      TY Γ ⊢ (Array x en T) : s
    (* | typed_arr_anon Γ en T s:
      sort s →
      TY Γ ⊢ en : Nat →
      TY Γ ⊢ T : s →
      TY Γ ⊢ (Array BAnon en T) : s *)
    | typed_pack Γ x en e T U:
      TY Γ ⊢ en : Nat →
      TY (insert_name x (App Idx en) Γ) ⊢ e : T →
      normal_eval (Array x en T) U →
      TY Γ ⊢ (Pack x en e) : U
    (* | typed_pack_anon Γ en e T:
      TY Γ ⊢ en : Nat →
      TY Γ ⊢ e : T →
      TY Γ ⊢ (Pack BAnon en e) : (Array BAnon en T) *)
    | typed_extract_array Γ e ei en T x T':
      (* transitively, we know en:Nat *)
      TY Γ ⊢ e : (Array x en T) →
      TY Γ ⊢ ei : (App Idx en) →
      (* we again handle named and unnamed simultanously *)
      normal_eval (subst' x ei T) T' →
      TY Γ ⊢ (Extract e ei) : T'
    | typed_extract_tuple Γ e ei Ts Ts' Ts'' T n s U:
      TY Γ ⊢ e : (Sigma Ts) →
      n = length Ts →
      TY Γ ⊢ ei : (App Idx n) →
      Ts' = close_subst e n Ts →
      Forall2 normal_eval Ts' Ts'' →
      normal_eval (Tuple Ts'') T →
      TY Γ ⊢ T : s ->
      normal_eval (Extract T ei) U ->
      TY Γ ⊢ (Extract e ei) : U *)

with type_assignable : typing_context -> expr -> expr -> Prop :=
  | assignable_typed Γ e T:
      TY Γ ⊢ e : T ->
      (* TY Γ ⊢ T ← e  *)
      type_assignable Γ T e
  (* | assignable_sigma Γ n Ts Ts'' e:
      (* 
        TODO:
        e#in is assignable to T_i under subst for all previous e
      *)
      n = length Ts ->
      let Ts' := close_subst e n Ts in
      Forall2 normal_eval Ts' Ts'' ->
      (* Note: extracts can not be inlined, it need intransparency *)
      let es' := extracts n e in
      Forall2 (type_assignable Γ) Ts'' es' ->
      type_assignable Γ (Sigma Ts) e *)
where "'TY' Γ ⊢ e : A" := (syn_typed Γ e%E A%E)
(* and "'TY' Γ ⊢ A ← e" := (type_assignable Γ A%E e%E) *)
.
#[export] Hint Constructors syn_typed : core.




(*
Thoughts on tuple types: do they make sense?

(bool, λ (x:bool) : Nat, if x then 1 else 0) : [Bool, Bool -> Nat]
(bool, λ (x:bool) : Nat, if x then 1 else 0) : [T:*, Π x:T, Nat] (or [T:*, T -> Nat])
(T, λ (x:T) : Nat, 42) : [T:*, Π x:T, Nat]

  |- bool : * (via app, Idx, Nat)
    x:bool |- Nat <- if x then 1 else 0
  |- λ (x:bool) : Nat, if x then 1 else 0 : Π x:bool, Nat
    T = [*, Π x:bool, Nat]
  [*, Π x:bool, Nat] ▹ T
|- (bool, λ (x:bool) : Nat, if x then 1 else 0) : T

has type [*, Π x:bool, Nat]
but we probably would want unifiable type [T:*, T -> Nat]

assume we want to put this into a function expecting [T:*, T -> Nat]
then our expression should be assignable via
  |- bool: * 
    |- λ (x:bool) : Nat, if x then 1 else 0 : Π x:bool, Nat
  |- (T -> Nat).[bool/T] <- λ (x:bool) : Nat, if x then 1 else 0
|- [T:*, T -> Nat] <- (bool, λ (x:bool) : Nat, if x then 1 else 0)

so at application point, it works out
*)












(* TODO: why do we need this proof? *)
(* Lemma syn_typed_closed Γ e A X :
  TY Γ ⊢ e : A →
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e.
Proof.
  (* remember e as e'. *)
  induction 1 in X |-*;simpl; intros Hx; try done.
  { (* var *) apply bool_decide_pack, Hx. apply elem_of_dom; eauto. }

  { (* Pi *)
    apply andb_True; split; try naive_solver.
    apply IHsyn_typed2. intros y. rewrite elem_of_dom lookup_insert_is_Some.
    intros [->|[? Hin]]. 
    - left.
    - right. apply Hx. apply elem_of_dom. assumption.
  }
  all: try (apply andb_True; split; try naive_solver).
  { (* Lam front stuff *)
    apply andb_True; split.
    1: apply andb_True; split.
    - naive_solver. 
    - apply IHsyn_typed3;intros x0.
    rewrite elem_of_dom lookup_insert_is_Some; intros [->|[? Hin]].
      + left.
      + right. now apply Hx, elem_of_dom. 
    - apply IHsyn_typed2;intros x0.
      rewrite elem_of_dom lookup_insert_is_Some; intros [->|[? Hin]].
      + left.
      + right. now apply Hx, elem_of_dom.
  }
  { (* Lam body *)
    (* TODO: need mutual induction for type assignable to solve e *)
    admit.
  }
  { (* lam anon body *)
  admit.
  }
  {
    (* app argument *)
    (* TODO: needs assignable induction *)
    admit.
  }
  {
    (* sigma *)  
    (* TODO: needs nested induction for sigma *)
    admit.
  }
  {
    (* TODO: needs nested induction for sigma *)
    admit.
  }
  {
    (* array *)
    apply IHsyn_typed2;intros x0. 
    rewrite elem_of_dom. 
    rewrite lookup_insert_is_Some.
    intros [->|[? Hin]].
    - left.
    - right.
    apply Hx. apply elem_of_dom. assumption.
  }
  {
    (* pack (the same again) *)
    apply IHsyn_typed2;intros x0. 
    rewrite elem_of_dom. 
    rewrite lookup_insert_is_Some.
    intros [->|[? Hin]].
    - left.
    - right.
    apply Hx. apply elem_of_dom. assumption.
  }
Admitted. *)

(*
Derive the mutual induction principles for syn_typed and type_assignable
*)
Scheme syn_typed_mut := Induction for syn_typed Sort Prop
with type_assignable_mut := Induction for type_assignable Sort Prop.

Combined Scheme typed_ind from syn_typed_mut, type_assignable_mut.

Lemma typed_weakening_mut:
  (forall Γ e A (H:TY Γ ⊢ e : A),
    forall Δ,
    Γ ⊆ Δ →
    TY Δ ⊢ e : A) /\
  (forall Γ A e (H:type_assignable Γ A e),
    forall Δ,
    Γ ⊆ Δ →
    type_assignable Δ A e).
  (* (TY Γ ⊢ e : A →
  TY Δ ⊢ e : A) /\
  (type_assignable Γ A e →
  type_assignable Δ A e). *)
Proof.
  eapply typed_ind with 
    (P := fun Γ e A H => 
      forall Δ, Γ ⊆ Δ ->
      TY Δ ⊢ e : A
    )
    (P0 := fun Γ A e H => 
      forall Δ, Γ ⊆ Δ ->
      type_assignable Δ A e
    ).
  all: intros.
  all: eauto.
  - (* var *) 
    (* intros x A sA Hlookup Hty IH. *)
    econstructor. by eapply lookup_weaken. 
  - (* pi *) 
    econstructor; eauto.
    eapply H0. destruct x;simpl;eauto using insert_mono. 
  - (* lam *) econstructor;destruct x; eauto using insert_mono.
  (*
  - (* sigma *)
    econstructor;destruct x;eauto using insert_mono.
  - (* Tuple *)
    econstructor;eauto.
    admit. (* needs nested induction for sigma *)
  - (* Array *)
    econstructor; eauto.
    apply H0.
    destruct x; eauto using insert_mono.
  - (* Pack *)
    econstructor; eauto.
    apply H0.
    destruct x; eauto using insert_mono.
  *)
  - (* assignable *)
    constructor;eauto.
  (*
  - (* assignable Sigma *)
    subst; subst Ts' es'.
    eapply assignable_sigma.
    2: eassumption.
    + reflexivity.
    + admit. (* needs nested induction *)
  *)
(* Admitted. *)
Qed.

Corollary typed_weakening Γ Δ e A:
  TY Γ ⊢ e : A →
  Γ ⊆ Δ →
  TY Δ ⊢ e : A.
Proof.
  destruct typed_weakening_mut.
  intros.
  eapply H;eauto.
Qed.


(* Lemma typed_weakening Γ Δ e A:
  TY Γ ⊢ e : A →
  Γ ⊆ Δ →
  TY Δ ⊢ e : A.
Proof.
  induction 1 in Δ |-*; intros Hsub; eauto.
  - (* var *) econstructor. 1: by eapply lookup_weaken. apply IHsyn_typed. done.
  - (* pi *) econstructor; eauto.
    eapply IHsyn_typed2. apply insert_mono. done.
  - (* lam *) econstructor; eauto using insert_mono.
    admit. (* needs mutual induction with type_assignable *)
  - (* lam anon *)
    econstructor; eauto.
    admit. (* needs mutual induction with type_assignable *)
  - (* app *)
    econstructor.
    + apply IHsyn_typed. done.
    + admit. (* needs assignable induction *)
  - (* sigma *)
    econstructor; eauto.
    apply IHsyn_typed2.
    now apply insert_mono.
  - (* Tuple *)
    econstructor.
    all: admit. (* needs nested induction for sigma *)
  - (* Array *)
    econstructor; eauto.
    apply IHsyn_typed2.
    now apply insert_mono.
  - (* Pack *)
    econstructor; eauto.
    apply IHsyn_typed2.
    now apply insert_mono.
Admitted. *)



(** Typing inversion lemmas 
what do we know from expression is typed
(expression specific everything else generic)

usually, we want those lemmas 
e.g. for substitution
however, we need dependent induction as we need inductive knowledge about 
the type derivations for types => any expression induction is insufficient
=> we derive these inversion lemmas on the fly


Lemma var_inversion Γ (x: string) A: TY Γ ⊢ x : A → 
  exists sA, Γ !! x = Some A ∧ TY Γ ⊢ A : sA.
Proof. inversion 1; subst; eauto. Qed.
*)


(* 

Lemma pi_inversion Γ T x U s:
  TY Γ ⊢ (Pi (BNamed x) T U) : s →
  ∃ sT sU, TY Γ ⊢ T : sT ∧ TY (<[x := T]> Γ) ⊢ U : sU ∧ kind_dominance [sT; sU] s.
Proof. inversion 1; subst; eauto. Qed.

Lemma pi_anon_inversion Γ T U s:
  TY Γ ⊢ (Pi BAnon T U) : s →
  ∃ sT sU, TY Γ ⊢ T : sT ∧ TY Γ ⊢ U : sU ∧ kind_dominance [sT; sU] s.
Proof. inversion 1; subst; eauto. Qed.

(* larger eauto to instantiate sT and sU correctly *)
Lemma lam_inversion Γ x T ef U e C:
  TY Γ ⊢ (Lam (BNamed x) T ef U e) : C →
  exists sT sU,
  C = (Pi (BNamed x) T U) ∧
  TY Γ ⊢ T : sT ∧
  TY (<[x := T]> Γ) ⊢ U : sU ∧
  TY (<[x := T]> Γ) ⊢ ef : Bool ∧
  type_assignable (<[x := T]> Γ) U e.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lam_anon_inversion Γ T ef U e C:
  TY Γ ⊢ (Lam BAnon T ef U e) : C →
  exists sT sU,
  C = (Pi BAnon T U) ∧
  TY Γ ⊢ T : sT ∧
  TY Γ ⊢ U : sU ∧
  TY Γ ⊢ ef : Bool ∧
  type_assignable Γ T e.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion Γ e eT B':
  TY Γ ⊢ (App e eT) : B' →
  ∃ x T U,
  B' = (subst' x eT U) ∧
  TY Γ ⊢ e : (Pi x T U) ∧
  type_assignable Γ T eT.
Proof. inversion 1; subst; eauto 10. Qed. *)





(*
closed under Γ then also under Δ

(inverse weakening)
could be helpful, but where is applies, a simple inversion
is usually easier/faster
*)
(* Lemma syn_typed_weakening Γ Δ e A X:
  TY Δ ⊢ e : A →
  Γ ⊆ Δ →
  (* is_closed (dom Γ) e → *)
  (∀ x, x ∈ dom Γ → x ∈ X) →
  is_closed X e →
  TY Γ ⊢ e : A.
*)


(*
  Lemmas that come up at some points and are helpful to have extra to clean up the proof
  Especially since we only use kind_dominance binary, 
  a subst idempotency lemma specialized for this case is helpful
*)
(* Lemma kind_subst_invariant xs s x es:
  kind_dominance xs s →
  subst x es s = s /\ Forall (λ s, subst x es s = s) xs.
Proof.
  induction 1;simpl;split;try destruct IHkind_dominance.
  all: eauto.
Qed. *)

(* Corollary kind_subst_invariant_apply s1 s2 s x es:
  kind_dominance [s1;s2] s →
  kind_dominance [subst x es s1;subst x es s2] (subst x es s).
Proof.
  intros H. 
  pose proof H.
  apply kind_subst_invariant with (x:=x)(es:=es) in H as [H1 H2].
  inversion_clear H2.
  inversion_clear H3.
  rewrite H1. rewrite H. rewrite H2.
  assumption.
Qed. *)


(*
Specialization to subst for fmap_insert since Coq won't recognize (subst a e') as function application point
*)
Corollary subst_map x a e' T Γ:
<[x:=subst a e' T]> (subst a e' <$> Γ) = subst a e' <$> (<[x:=T]> Γ).
Proof.
  now rewrite fmap_insert.
Qed.

Corollary insert_subst_map x a e' T Γ:
insert_name x (subst a e' T) (subst a e' <$> Γ) = subst a e' <$> (insert_name x T Γ).
Proof.
  destruct x;eauto using subst_map.
Qed.

(*
  Substitution reordering to distrubte the subst from typing predicates to the outside
  for induction hypotheses
*)
Lemma subst_distr x a e1 e2 e3:
  a ≠ x →
  subst a e1 (subst x e2 e3) = subst x (subst a e1 e2) (subst a e1 e3).
Proof.
  (* induction e';simpl;eauto 10.
  - destruct decide;subst;simpl;eauto;destruct decide;subst;eauto;simpl.
  all: admit.
  -  *)
  intros Hneq.
  induction e3;simpl;try congruence.
  - destruct (decide) as [Heq|Heq];simpl.
    + rewrite Heq. 
      destruct decide;try congruence.
      simpl.
      now destruct decide;congruence.
    + destruct decide as [Heq'|Heq'].
      * admit. 
      * simpl. destruct decide;congruence.
  (* ... *)
Admitted.

Corollary subst'_distr x a e1 e2 e3:
  BNamed a ≠ x →
  subst a e1 (subst' x e2 e3) = subst' x (subst a e1 e2) (subst a e1 e3).
Proof.
  intros H.
  destruct x;simpl.
  - reflexivity.
  - apply subst_distr.
    contradict H. congruence.
Qed.


(*
Substitution lemmas
|- e' : A
Γ, x : A ⊢ e : B
=================
Γ ⊢ e[e'/x] : B[e'/x]

Note: Importantly, we need to substitute in the type as well as it might contain/depend on the variable x.

Also see page 55 in
https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf
*)
Lemma typed_substitutivity e e' Γ (a: string) A B :
  TY ∅ ⊢ e' : A →
  TY (<[a := A]> Γ) ⊢ e : B →
  (* TODO: replace in Gamma/ use Γ, x:A, Δ  (some common prefix of all typing derivations here) *)
  (* TY Γ ⊢ lang.subst x e' e : lang.subst x e' B. *)
  TY ((subst a e') <$> Γ) ⊢ lang.subst a e' e : lang.subst a e' B.
  (*
  TODO: a can be free in e (whole idea of this lemma)
  however, a should not clash with a binder (why?) as it ruins the induction hypothesis
  *)
Proof.
    (*
    TODO: need A is closed under Γ by closed typing => subst does nothing
    same for Gamma (maybe as assumption)
    *)
  assert (lang.subst a e' A = A) as HsubstA by admit.
  intros He' H.
  (* 
  induction e + inversion lemmas alone are not enough due to dependencies
  subst B : ... is missing => needs hypothesis 
  *)
  dependent induction H;simpl;eauto.
  - (* var *)
    destruct decide;subst.
    + rewrite lookup_insert in H. inversion H;subst. 
      rewrite HsubstA.
      eapply typed_weakening;first eassumption.
      apply map_empty_subseteq.
    + econstructor.
      rewrite lookup_insert_ne in H; eauto.
      now rewrite lookup_fmap H;simpl.
  - (* Pi *)
    econstructor.
    + eapply IHsyn_typed1; eauto.
    + destruct decide.
      * symmetry in e. inversion e ;subst.
        (* replace (<[a:=subst a e' T]> (subst a e' <$> Γ)) with ((subst a e') <$> (<[a:=T]> Γ)) by apply fmap_insert. *)
        (* TODO: we should not subst under U => need to know that x already bounds? *)

        (* TODO: do we need to rule this case out (binder same name as subst variable?) or do we need stronger subst statements about expression/type subst (maybe independent) *)
        admit. (* TODO: name clash *)
      * rewrite insert_subst_map.
        eapply IHsyn_typed2;eauto.
        destruct x;eauto using insert_commute with congruence.
  - (* Lambda named *)
    simpl in IHsyn_typed1.
    specialize (IHsyn_typed1 Γ a A).
    destruct decide.
    + (* TODO: name clash should not happen *)
      admit.
    + econstructor.
      * eapply IHsyn_typed1;eauto.
      * rewrite insert_subst_map.
        eapply IHsyn_typed2;eauto.
        destruct x;eauto using insert_commute with congruence.
      * admit. (* needs assignable induction *)
  - (* App *)
    (* rewrite subst'_distr.
    2: {
      admit. (* TODO: no name clash *)
    } *)
    eapply typed_app.
    + cbn in IHsyn_typed.
      specialize (IHsyn_typed Γ a A).
      (* TODO: no name clash *)
      replace (if decide (x = a) then U else subst a e' U) with (subst a e' U) in IHsyn_typed by admit.
      apply IHsyn_typed;eauto.
    + admit. (* needs assignable induction *)
    + admit. (* normalize TODO: *)
  - (* Sigma *)
    econstructor.
    + eapply IHsyn_typed1;eauto.
    + rewrite insert_subst_map.
      specialize (IHsyn_typed2 (insert_name x T Γ) a A).
      simpl in IHsyn_typed2.
      destruct decide.
      1: admit. (* TODO: no name clash *)
      apply IHsyn_typed2;eauto.
      destruct x;eauto using insert_commute with congruence.
  - (* Tuple *)
    apply typed_tuple with (Ts:=map (subst a e') Ts).
    + admit.
      (* 
        we know 
          Sigma Ts ->n T
        we want
          Sigma ? ->n T[e'/a]

        TODO: need nested induction
        for substing in each T
      *)
    + admit.
      (*
        want to show that Sigma (subst Ts) ->n subst T
        e.g. normalization is subst invariant 
        TODO: does this even hold?
        subst could allow for additional normalizations
      *)
  - (* Array *)
    econstructor.
    (* + destruct H;subst;simpl;[now left|now right]. *)
    + eapply IHsyn_typed1;eauto.
    + change (Idx (subst a e' en)) with (subst a e' (Idx en)).
      rewrite insert_subst_map.
      destruct decide.
      1: admit. (* TODO: no name clash *)
      eapply IHsyn_typed2;eauto.
      destruct x;eauto using insert_commute with congruence.
  - (* Pack *)
    econstructor.
    + eapply IHsyn_typed1;eauto.
    + change (Idx (subst a e' en)) with (subst a e' (Idx en)).
      rewrite insert_subst_map.
      destruct decide.
      1: admit. (* TODO: no name clash *)
      eapply IHsyn_typed2;eauto.
      destruct x;eauto using insert_commute with congruence.
    + admit. (*
      need normalize_eval also Array
      TODO: does this hold?
    *)
  - (* Extract array *)
    (* rewrite subst'_distr.
    2: {
      admit. (* TODO: no name clash *)
    } *)
    eapply typed_extract_array.
    + specialize (IHsyn_typed1 Γ a A).
      simpl in IHsyn_typed1.
      destruct decide.
      1: admit. (* TODO: no name clash *)
      eapply IHsyn_typed1;eauto.
    + change (Idx (subst a e' en)) with (subst a e' (Idx en)).
      eapply IHsyn_typed2;eauto.
    + admit. (* TODO: normalize *)
  - (* Extract tuple *)
    eapply typed_extract_tuple with (n:=length Ts).
    1: {
      simpl in IHsyn_typed1.
      eapply IHsyn_typed1;eauto.
    }
    3: reflexivity.
    2: {
      eapply IHsyn_typed2;eauto.
    }
    4: {
      eapply IHsyn_typed3;eauto.
    }
    all: admit. (* normalize under subst TODO: with additional normalize *)
Admitted.



(*
canonical values (see one from above for Idx)
(specific type, rest generic, and is value expression)

  e : Idx #n 
e : Idx en (unnecessary?)
  e : Array x en T (changes under normalization lemma)
  e : Sigma Ts
  e : Pi x T U
  e : Nat
*)

(* Lemma canonical_kind xs s:
  kind_dominance xs s →
  sort s.
Proof.
  intros H.
  induction H;auto;firstorder.
Qed. *)

(* all general cases that are contradictory 
  manually identified while proving the canonical value idx lemma
*)
Ltac no_nonsense_canonical := 
  first 
  [
    (*
      Look for assumption sort (...) where the inner is not Star or Box
      try to apply inversion;congruence

      Array named/anon
    *)
    (* match goal with
    | H: sort ?s |- _ => try (inversion H;congruence)
    end
  | *)
    (*
      Look for assumption kind_dominance xs s where s is not Star, Box or a variable
      apply canonical_kind;congruence

      Pi named/anon, Sigma named/anon
    *)
    (* match goal with
    | H: kind_dominance ?xs ?s |- _ => try (apply canonical_kind in H as [];congruence)
    end
  | *)
    (* 
    find an illegal Idx expression as function value
    e.g.
    H0: TY Γ ⊢ Idx : Pi x T U
    H: subst' x #n U = X
    where X is not star
    => we need to find two assumptions that contradict

    Idx #n as value via App case
    *)
      (* idtac "found1"; *)
    match goal with
    | H0: (TY ?Γ ⊢ Idx : Pi ?x ?T ?U),
      H: (subst' ?x ?e ?U = ?X)
      |- _ => 
      (* idtac "found" *)
      try (inversion H0;subst;simpl in H;congruence)
    end
  ].



(* is it sufficient to have n fixed as a nat or do we want more generally ⊢ en : Nat *)
Lemma canonical_value_idx Γ e (n:nat):
  TY Γ ⊢ e : Idx (LitNat n) ->
  is_val e ->
  exists i, e = LitIdx n i.
Proof.
  intros Hty Hv.
  inversion Hty;subst;try naive_solver;inversion Hv;subst;try no_nonsense_canonical.
  inversion H;subst.
  simpl in H1.
  admit. (* Star does not normalize to Idx *)
  (* 
  - exfalso. admit. (* Sigma will only every normalize to Sigma (not Idx) *)
  - exfalso. admit. (* Same with Array *)
  *)
Admitted.

(*
  We take a look at a (possibly) interesting example to get a feeling for the type system
  There is no invalid extract.
  Especially, we never can extract from an empty tuple
*)
(* Example untyped_empty_extract:
    (* we might as well assume ei is a value
      (by soundess, we can evaluate to a value)
    *)
  ~ (exists Γ ei T, 
      (* Simplifying assumption (see above) *)
      is_val ei /\
      (* TODO: is it valid to assume that T is also a value? *)
      (* is_val T /\ *)
      TY Γ ⊢ (Extract (Tuple []) ei) : T).
Proof.
  intros (Γ&ei&T&(Hv&Hty)).
  inversion Hty;subst.
  - (* array extract *)
    (* we have Tuple [] : Array x en T0 *)
    (* => the nat literal en is a nat 0 *)
    inversion H2;subst;clear H2.
    inversion H0;subst;clear H0.
    simpl in H3.
    admit. (* TODO: 
      Sigma [] ->n <<n;?>>
      where result is <<x:en;T>>
      => x = Anon, en = 0, T = ? (anything)
      do we want n > 0?
    *)
     (* TODO: this currently just works because normalization is not implemented *)
  - (* sigma tuple extract *)
    (*
      proof idea:
      ei is a Idx 0
      because length Ts = 0 where Ts is the sigma type
    *)
    clear Hty.
    assert (Ts = []) as ->.
    {
      inversion H1;subst.
      inversion H0;subst.
      simpl in *.
      inversion H4;subst.
      (*  
        TODO: either Sigma [] ->n Sigma Ts
        is contradictory or Ts = []
      *)
      (* done. *)
      admit.
    }
    simpl in H3.
    pose proof (canonical_value_idx _ _ _ H3 Hv) as [i ->].
    inversion i.
Admitted. *)

Lemma canonical_value_pi Γ e x T U:
  TY Γ ⊢ e : Pi x T U →
  is_val e ->
  
  (e = Idx ∧ x = BAnon /\ T = Nat ∧ U = Star) ∨
  exists f ef, 
    (e = Lam x T f U ef).
Proof.
  intros Hty Hv.
  inversion Hty;subst;try naive_solver;inversion Hv;subst;try no_nonsense_canonical.
  inversion H;subst.
  admit. (* Star does not normalize to Pi *)
  (*
  - (* lambda named *)
    right. eauto.
  - (* lambda anon *)
    right. eauto.
  - exfalso. admit. (* Sigma will only every normalize to Sigma (not Pi) *)
  - exfalso. admit. (* Same with Array *)
  *)
Admitted.

Lemma canonical_value_nat Γ e:
  TY Γ ⊢ e : Nat →
  is_val e ->
  
  exists n, e = LitNat n.
Proof.
  intros Hty Hv.
  inversion Hty;subst;try naive_solver;inversion Hv;subst; try no_nonsense_canonical.
  inversion H;subst.
  admit. (* Star does not normalize to Nat *)
  (*
  - exfalso. admit. (* Sigma will only every normalize to Sigma (not Nat) *)
  - exfalso. admit. (* Same with Array *)
  *)
Admitted.

(* Lemma canonical_value_sigma Γ e Ts:
  TY Γ ⊢ e : Sigma Ts →
  is_val e ->
  
  (exists es, e = Tuple es 
    /\ Forall is_val es
    /\ length es = length Ts) \/
  (exists x e',
    e = Pack x (LitNat (length Ts)) e'
  ).
  (* TODO: do we know anything about e' *)
    (* /\ Forall2 (λ e '(x,T), TY Γ ⊢ e : T) es Ts.  *)
    (* not needed *)
Proof.
  intros Hty Hv.
  inversion Hty;subst;try naive_solver;inversion Hv;subst; try no_nonsense_canonical.
  + (* 
    Sigma -> Sigma normalization
    TODO: need additional lemma that normalization preserves at least the length
  *)
    left.
    eexists.
    split;[reflexivity|].
    split;[assumption|].
    admit.
    (* inversion H0;subst;clear H0.
    clear Hty H2 Hv. *)
    (*
    induction H;simpl;split;auto;destruct IHForall2;auto.
    - exfalso. admit. (* Sigma will only every normalize to Sigma (not Nat) *)
    - exfalso. admit. (* Same with Array *)
    *)
  + (* pack whose array type was normalized into sigma *)
    right.
    do 2 eexists;f_equal;eauto.
    pose proof (canonical_value_nat _ _ H H3) as [n ->].
    admit. (* TODO: need that normalization Array to Sigma preserves length *)
Admitted. *)


(* Definition add_binder x e Γ := 
  match x with
  | BAnon => Γ
  | BNamed x => <[x:=e]> Γ
  end.
Transparent add_binder. *)


(* TODO: this changes with normalization *)
(* Lemma canonical_value_array Γ e x en T:
  TY Γ ⊢ e : Array x en T ->
  is_val e ->
  
  exists eb,
    e = Pack x en eb
    /\ is_val en
    /\ TY Γ ⊢ en : Nat
    /\ TY (insert_name x (Idx en) Γ) ⊢ eb : T.
Proof.
  intros Hty Hv.
  inversion Hty;subst;simpl.
  all: inversion Hv;subst;simpl;try no_nonsense_canonical.
  - (* TODO: Tuple could be pack (if Sigma normalized to array) *)
    admit.
  - eexists;repeat split. 
    all: admit. 
    (*
      TODO: needs normalization lemmas
      that Array -> Array then the vars are the same
    *)
  - (* Pack anon *)
    eauto 10.
Admitted. *)






(*
Progress 
|- e : A
=================
e is a value or
exists e' s.t. e -> e'
*)

(*
  we now go under binder => need Γ
*)

Lemma typed_progress_mut:
  (* everything except var works out with Γ instead of ∅ *)
  (forall Γ e A (H:TY Γ ⊢ e : A),
    (* Γ = ∅ -> *)
    (* (exists x, e = Var x) \/ *)
    is_val e ∨ reducible e) /\
  (forall Γ A e (H:type_assignable Γ A e),
    (* Γ = ∅ -> *)
    is_val e ∨ reducible e).
Proof.
  eapply typed_ind;intros;subst;eauto 10 using is_val.
  (* 
  - (* var *)
    (* inversion e. *)
    left. constructor.
  *)
  - (* Lambda *)
    destruct H1 as [HvalT|[? ?]].
    + left. now constructor.
    + right. eexists. eauto.
      (* destruct H1 as [e' [K ? ? -> -> Hstep]].
      eexists.
      eapply Ectx_step with (K:= LamCtx x T ef U K);eauto. *)
  - (* App *)
    destruct H.
    + destruct H0.
      * (* canonical value *)
        specialize (canonical_value_pi _ _ _ _ _ s H) as [(->&->&->&->)|(f&ef&->)].
        -- (* canonical value Idx *)
          inversion t;subst.
          specialize (canonical_value_nat _ _ H1 H0) as [m ->].
          left. constructor.
        -- right.
          eexists. eapply base_contextual_step.
          eapply BetaS. reflexivity.
      * right. destruct H0.
        eexists. eauto.
    + right. destruct H.
      eexists. eauto.
Qed.
(*
  - (* pi *)
    destruct H;eauto.
    + left. now constructor.
    + destruct H. right. eexists. 
      eauto. (* uses contextual step lemmas *)
  - (* pi anon *)
    destruct H;eauto.
    + left. now constructor.
    + destruct H. right. eexists. 
      eauto.
  - (* lambda *)
    destruct H;eauto.
    + left. now constructor.
    + destruct H. right. eexists. 
      eauto. (* uses contextual step lemmas *)
  - (* lambda anon -- same as named *)
    destruct H;eauto.
    + left. now constructor.
    + destruct H. right. eexists. eauto. 
  - (* app *)
    destruct H;eauto.
    + destruct H0 as [HvalT|HredT];eauto.
      * specialize (canonical_value_pi _ _ _ _ _ s H) as [(->&->&->&->)|(f&ef&(->&HvT))].
        -- (* canonical value Idx *)
          left.
          inversion t;subst.
          (* from type_assignable, we get
            eT: Nat (by inversion on eT is Nat assignable)
            from there and canonical value, eT = LitNat n
            hence, IdxAppV applies
          *)
          specialize (canonical_value_nat _ _ H0 HvalT) as [n ->].
          now constructor.
        -- right. 
          (* e: Pi x T U /\ is_val e => canonical form *)
          eexists. eapply base_contextual_step.
          eapply BetaS. 3: reflexivity. 
          all: try eassumption.
          admit. (* here, we are in lambda app, where left are values
            but we need normalized =>
            TODO: lemma needs to talk about normalization (either it is normalized or normalization possible)

            we have:
            is_val T
            is_val eT

            ⊢ λ (x:T) : U, ef : Pi x T U

            we want normalized T
           *)
      * right. destruct HredT. eexists. eauto. 
    + right. destruct H. eexists. eauto. 
  - (* sigma cons *)
    destruct H;eauto.
    + (* we only perform head reduction at sigma => rest not relevant *)
      left. now constructor.
    + right. destruct H. eexists. eauto. (* contextual step lemma *)
  - (* sigma anon cons -- identical to sigma cons *)
    destruct H;eauto.
    + left. now constructor.
    + right. destruct H. eexists. eauto. (* contextual step lemma *)
  - (* tuple *)
    admit. (* missing nested induction *)
  - (* array *)
    destruct H;eauto.
    + (* T is not reduced as it (might) depend on x *)
      left. now constructor.
    + right. destruct H. eexists. eauto. (* contextual step lemma *)
  - (* array anon -- identical to array *)
    destruct H;eauto.
    + left. now constructor.
    + right. destruct H. eexists. eauto. (* contextual step lemma *)
  - (* pack *)
    destruct H;eauto.
    + left. now constructor.
    + right. destruct H. 
      eexists. eauto.
  - (* pack anon -- identical to pack *)
    destruct H;eauto.
    + left. now constructor.
    + right. destruct H. eexists. eauto. (* contextual step lemma *)
  - (* extract array *)
    destruct H;eauto.
    + destruct H0;eauto.
      * right.
        pose proof (canonical_value_array _ _ _ _ _ s H) as [eb (->&Hvalen&Htyen&Htyeb)].
        (* from array, we get that en is a value from there, we get the idx value *)
        pose proof (canonical_value_nat _ _ Htyen Hvalen) as [n ->].
        pose proof (canonical_value_idx _ _ _ s0 H0) as [i ->].
        eexists.
        apply base_contextual_step.
        apply IotaPackS.
        2: reflexivity.
        assumption.
      * right. destruct H0. eexists. eauto. 
    + right. destruct H. eexists. eauto. 
  - (* extract tuple (sigma type) *)
    subst;simpl.
    destruct H;eauto.
    + destruct H0;eauto.
      * right.
        pose proof (canonical_value_idx _ _ _ s1 H0) as [i ->].
        pose proof (canonical_value_sigma _ _ _ s0 H) as [[es (->&Hval&Hlen)]|].
        -- (* a tuple as expected *)
          pose proof (nth_fin _ es).
          rewrite Hlen in H2; specialize (H2 i); destruct H2.
          eexists.
          apply base_contextual_step.
          (* IotaTupleS -- we know that e has to be a tuple as a pack will always have array type *)
          apply IotaTupleS.
          ++ assumption.
          ++ assumption.
          ++ apply H2.
        -- destruct H2 as (x&eb&->).
          (* a pack instead that was normalized *)
          eexists.
          apply base_contextual_step.
          apply IotaPackS;eauto.
      * right. destruct H0. eexists. eauto. 
    + right. destruct H. eexists. eauto.
  - (* type assignable sigma *)
    subst Ts' es'.
    admit. (* needs nested induction *)
    (* and type assignable inversion lemma? 
      we have 
        type_assignable ∅ (Ti[...]) (ei#i)
      by induction, we get
        is_val ei#i  or reducible ei#i
      (which is reducible for all because a projection is never a value)
      giving us nothing for e

      TODO:
      should we speak about normalization here?
        normalized e 
      is not enough, because we have the problem with the unreduced assignable cases
      => maybe reformulate as
      type_assignable Γ A e ->
      normalized e e' ->
      is_val e' ∨ reducible e'
    *)
Admitted.
*)

Corollary typed_progress e A:
  (* everything except var works out with Γ instead of ∅ *)
  TY ∅ ⊢ e : A →
  is_val e ∨ reducible e.
Proof.
  edestruct typed_progress_mut as [H _];eauto.
Qed.




Lemma Forall2_nth_error {X Y:Type} (P: X -> Y -> Prop) xs ys:
  Forall2 P xs ys →
  (* ∀ i x y, xs !! i = Some x → ys !! i = Some y → P x y. *)
  forall i x,
  (* xs !! i = Some x →
  exists y, ys !! i = Some y ∧ P x y. *)
  nth_error xs i = Some x →
  exists y, nth_error ys i = Some y ∧ P x y.
Proof.
  intros H i x Hx.
  induction H in i,Hx |-*;destruct i;simpl in *;try congruence.
  - inversion Hx;subst.
    exists y;split;eauto.
  - clear x0 y H.
    specialize (IHForall2 i Hx) as [y [Hy HP]].
    exists y;split;eauto.
Qed.
Arguments Forall2_nth_error {_ _ _ _ _}.



Lemma typed_preservation_base_step e e' A:
  TY ∅ ⊢ e : A →
  base_step e e' →
  TY ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep.
  inversion Hstep;subst.
  inversion Hty;subst;eauto using is_val.
  inversion H1;subst.
  inversion H3;subst. (* assignable *)



































Lemma typed_preservation_normal_step e e' A:
  TY ∅ ⊢ e : A →
  normalize_step e e' →
  exists A', TY ∅ ⊢ e' : A' ∧
  rtc normalize_step A A'.
Proof.
  intros Hty Hstep.
  induction Hstep in A, Hty |- *.
  all: inversion Hty;subst.
  - eexists;split;eauto.
    (*
      TODO: 
      e#0_1 => e
      e has Array type, but it is (eb) or <x:1;eB> or <1;eB> (can it be some n that is not one? (e.g. function call))
      is normalized (but not value)
      e might be ((lam x @bot) 1)

      => not even normalized enough to preserve type
    *)
  - eexists;split;eauto.
  - inversion H0;subst.
    eexists;eauto.
  - eexists. econstructor;eauto.
  - eexists. econstructor;eauto.
  - inversion H4;subst.
    specialize (Forall2_nth_error H1 _ _ H0) as [Ti [HTi Htyi]].
    (* TODO: do we need something about the normal_eval? *)
    eexists. eauto.
  - inversion H3;subst.
    specialize (Forall2_nth_error H1 _ _ H0) as [Ti [HTi Htyi]].
    (* TODO: do we need something about the normal_eval? *)
    eexists. eauto.
  - inversion H2;subst.
    eexists. eauto.
  - inversion H1.
  - (* eta tuple case *)
    eexists.
    admit.
    (* TODO: needs lemma that something has Sigma-like type (or at least a type for now), if each extract is typed *)
  - inversion H1;subst.
    + destruct n;simpl in *;[lia|congruence].
    + destruct n;try lia;simpl in *.
      inversion H0;subst.
      (* or inversion H1;subst. *)
      eexists. econstructor;eauto.
  - destruct n;simpl in *;[lia|congruence]. (* TODO: why is this contradictory *)
  - destruct n;simpl in *;try lia.
    inversion H0;subst. (* TODO: why is this contradictory *)
  - destruct n;simpl in *;try lia.
    inversion H0;subst.
    eexists. econstructor;eauto.
    inversion H4;subst;firstorder.
  - inversion H3;subst.
  (*
  assignable => has some (similar) type (not necessarily normal-equivalent)

  assignable ≃ (maybe nested) sigma replace by substed variant
  lambdas use assignable and extracts subst-close always
  *)
    + admit. (* subst with assignable? *)
    + simpl. admit. (* same but simpler *)
  - eexists. econstructor.
    all: admit. (* if typed with context => instantiate typed *)
  - admit. (* if typed with context => instantiate typed *)
Admitted.







Lemma typed_preservation_normal_step e e' A:
  TY ∅ ⊢ e : A →
  normalize_step e e' →
  exists A', TY ∅ ⊢ e' : A'.
(* and A' is normalize_reachable from A *)
Proof.
  intros Hty Hstep.
  induction Hstep in A, Hty |- *.
  all: inversion Hty;subst.
  - eexists;eauto.
  - eexists;eauto.
  - inversion H0;subst.
    eexists;eauto.
  - eexists. econstructor;eauto.
  - eexists. econstructor;eauto.
  - inversion H4;subst.
    specialize (Forall2_nth_error H1 _ _ H0) as [Ti [HTi Htyi]].
    (* TODO: do we need something about the normal_eval? *)
    eexists. eauto.
  - inversion H3;subst.
    specialize (Forall2_nth_error H1 _ _ H0) as [Ti [HTi Htyi]].
    (* TODO: do we need something about the normal_eval? *)
    eexists. eauto.
  - inversion H2;subst.
    eexists. eauto.
  - inversion H1.
  - (* eta tuple case *)
    eexists.
    admit.
    (* TODO: needs lemma that something has Sigma-like type (or at least a type for now), if each extract is typed *)
  - inversion H1;subst.
    + destruct n;simpl in *;[lia|congruence].
    + destruct n;try lia;simpl in *.
      inversion H0;subst.
      (* or inversion H1;subst. *)
      eexists. econstructor;eauto.
  - destruct n;simpl in *;[lia|congruence]. (* TODO: why is this contradictory *)
  - destruct n;simpl in *;try lia.
    inversion H0;subst. (* TODO: why is this contradictory *)
  - destruct n;simpl in *;try lia.
    inversion H0;subst.
    eexists. econstructor;eauto.
    inversion H4;subst;firstorder.
  - inversion H3;subst.
  (*
  assignable => has some (similar) type (not necessarily normal-equivalent)

  assignable ≃ (maybe nested) sigma replace by substed variant
  lambdas use assignable and extracts subst-close always
  *)
    + admit. (* subst with assignable? *)
    + simpl. admit. (* same but simpler *)
  - eexists. econstructor.
    all: admit. (* if typed with context => instantiate typed *)
  - admit. (* if typed with context => instantiate typed *)
Admitted.

Lemma typed_preservation_full_normal_step e e' A:
  TY ∅ ⊢ e : A →
  full_contextual_step e e' →
  exists A', TY ∅ ⊢ e' : A'.
(* and A' is normalize_reachable from A *)
Proof.
  intros Hty Hstep.
  destruct Hstep as [K e1' e2' -> -> Hstep].
  induction K in A, Hty |- *;simpl in *.
  1: eapply typed_preservation_normal_step;eauto.
  all: inversion Hty;subst.
  - edestruct IHK;eauto.
    eexists. econstructor.
    + eauto.
    + admit. (* step in context,  *)
    + admit. (* non trivial sort/kind reasoning *)
  - admit. (* same as previous case *)
  - (* pi step right *)
    admit. (* needs contexts for IH *)
  - admit. (* pi step right unnamed *)
  - (* lam ty *)
    eexists;econstructor.
    + admit. (* IH *)
    + admit. (* context step *)
    + admit. (* context step *)
    + admit. (* context step under assignable *)
  - (* lam ty unnamed *)
    admit.
  - (* lam filter *)
    eexists;econstructor.
    + eassumption.
    + eassumption.
    + admit. (* IH under context *)
    + eassumption.
  - (* lam filter unnamed *)
    admit.
  - admit. (* lam return type *)
  - admit. (* lam return type unnamed *)
  - admit. (* lam body *)
  - admit. (* lam body unnamed *)
  - (* app left *)
    edestruct IHK;eauto.
    eexists;econstructor.
    + admit. (* we need that the expression also is a pi => normal_form lemma would give this as Pi only normalizes to Pi *)
    + eassumption.
  - (* app right *)
    (* edestruct IHK;eauto. *)
    eexists;econstructor.
    + eassumption.
    + admit. (* need type assignability (mutual) strengthening *)
  - (* sigma empty context *)
    destruct xs1;simpl in *;congruence.
  - (* sigma *)
    assert(exists A, TY ∅ ⊢ full_fill K e1' : A) as [Te1' HTe1'].
    {
      admit. (* IH *)
    }
    edestruct IHK;eauto.
    admit.
  - (* sigma unnamed *)
    admit.
  - (* Tuple *)
    admit.
  - (* Array *)
    edestruct IHK;eauto.
    eexists;econstructor.
    2: admit. (* needs that the type of e2' is a nat => Nat only normalizes into nat *)
    eauto.
    admit. (* step in context *)
  - (* array unnamed *)
    admit.
  - (* Array body *)
    admit.
  - (* array body unnamed *)
    admit.
  - (* pack *)
    admit.
  - (* pack unnamed *)
    admit.
  - (* pack body *)
    admit.
  - (* pack body unnamed *)
    admit.
  - (* extract array left *)
    edestruct IHK;eauto.
    eexists;econstructor;eauto.
    admit. (* need that body has array type *)
  - (* extract tuple left *)
    admit.
  - (* extract array right *)
    admit.
  - (* extract tuple right *)
    admit.
Admitted.

Lemma typed_preservation_normal_eval e e' A A':
  TY ∅ ⊢ e : A →
  normal_eval e e' →
  (* normalize_step e e' → *)
  normal_eval A A' →
  (* normalize_step A A' → *)
  TY ∅ ⊢ e' : A'.
Proof.
  intros Hty HstepE HstepA.
  destruct HstepE as [HstepE HnormE].
  destruct HstepA as [HstepA HnormA].
  unfold normalized_pred in *.
  induction HstepE in A,A', Hty, HstepA, HnormA |- *.
  - admit.
  - eapply IHHstepE.
    3: apply HnormA.
    + clear e' z HstepE HnormE IHHstepE.
      (*
        e has some A'' s.t. A ->n A''
      *)
      admit.
    (* + clear IHrtc. *)
      (* clear H0 H3. *)
    + 
      (* 
        A'' ->n A'
        by A ->n A''
        and confluence/church-rosser we know that A'' ->n A'
      *)
      admit.
Admitted.
































(* Lemma typed_preservation_base_step e e' A:
  TY 0; ∅ ⊢ e : A →
  base_step e e' →
  TY 0; ∅ ⊢ e' : A.
Proof. *)

Lemma typed_preservation_base_step e e' A:
  TY ∅ ⊢ e : A →
  base_step e e' →
  TY ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep.
  inversion Hstep;subst.
  (* beta and 2 iota *)
  all: inversion Hty;subst;eauto using is_val.
  - (* beta *)
    (* unify lambda name and pi name *)
    inversion H4;subst.
    + (* named *)
      (* replace (∅) with (subst x1 earg <$> ∅). *)
      simpl.
      replace (TY ∅ ⊢ subst x1 earg elam : subst x1 earg U0)
      with (TY subst x1 earg <$> ∅ ⊢ subst x1 earg elam : subst x1 earg U0) by now rewrite fmap_empty.
      eapply typed_substitutivity.
      (* TODO: need full TY ... due to fmap value type parameter => use lemma 
        see lemma below
      *)
      * admit. 
      * admit. 
      (*
      TODO: 
        we know earg is assignable to T0
        and elam is under x1:T0 assignable to U0

        wa want 
        elam [earg/x1] : U0 [earg/x1]

        => subst lemma for assignable
        or assignable => typed
      *)
    + (* anon *)  
      simpl in *. (* remove all subst *)
      admit. (* TODO: needs assignable induction? here, elam is assignable T0 -- see above *)
  - (* Iota Tuple *)
    (* Tuple: Array *)

    inversion H4;subst.
    specialize (Forall2_nth_error H2 (` (Fin.to_nat i)) e' H1) as [T' [HnthT' HT']].
    (*
      we have 
      e' : T'
      with 
      nth Ts i = T'
      and Ts ->n <x:en;T>
      and want e' : T[x/Idx n i]

      TODO: need normalization on the type again
    *)
    admit.
  - (* Iota Tuple *)
    (* Tuple: Sigma *)
    inversion H3;subst.
    specialize (Forall2_nth_error H2 (` (Fin.to_nat i)) e' H1) as [T' [HnthT' HT']].
    (* 
    we have

    Ts0 ->n Ts
    Ts  ->n T
    T#i ->n A

    nth es  i = e'
    es : Ts0
    (result from this)
    nth Ts0 i = T'
    e' : T'

    es#i : A

    and want e' : A

    high-level:
    we extract from a tuple,
    we know the element in the tuple has some type
    now the typing rules for the tuple normalized the types

    the evaluation results in projecting one element out

    either:
    - this element has to be normalized (by the evaluation)
    - the lemma normalizes the element
    - normalization does not change the type because it is already a value (and normalized?)

    TODO: is there a normalization in the result missing?
     *)
    admit. 
  - (* Iota Pack *)
    (* Pack: Array *)
    inversion H3;subst.
    + (* named *)
      simpl in *.
      (* TODO: need normalization lemma Array -> Array *)
      replace T with T0 by admit.
      replace x0 with (BNamed x1) by admit.
      simpl.
      replace (TY ∅ ⊢ subst x1 ei e0 : subst x1 ei T0)
        with (TY subst x1 ei <$> ∅ ⊢ subst x1 ei e0 : subst x1 ei T0) by now rewrite fmap_empty.
      eapply typed_substitutivity;eauto.
      replace en with (LitNat n) by admit.
      eauto.
    + (* anon *)
      simpl in *.
      assumption.
  - (* Iota Pack *)
    (* Pack: Sigma *)
    inversion H2;subst.
    (*
      Ts -> close subst -> T -> extract -> A

      TODO: why does this hold?
      e0 should be subst invariant under the type named binders
      => subst lemma
    *)
    admit.
Admitted.


Definition ectx_typing (K: ectx) A B :=
  ∀ e, TY ∅ ⊢ e : A → TY ∅ ⊢ (fill K e) : B.

Lemma fill_typing_compose K e A B:
  TY ∅ ⊢ e : B →
  ectx_typing K B A →
  TY ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.



Lemma typed_preservation e e' A:
  TY ∅ ⊢ e : A →
  contextual_step e e' →
  TY ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].

  dependent induction Hty;eauto.
  all: destruct K;simpl in *;try congruence;subst.
  all: try now inversion Hstep.
  all: try inversion x;subst.
  - (* pi named *)
    eapply typed_pi;eauto.
    admit. (* step in context *)
  - (* pi anon *)
    admit.
  - (* lambda named *)
    (* the type is normalized *)
    (*
      TODO: new insight => see head in lang
    *)


    eapply beta_typed.
    2: eapply Ectx_step with (K:=PiCtx x0 K U0);eauto.
    simpl.
    eapply beta_typed_lam;eauto.
    + admit. (* step in context *)
    + admit. (* step in context *)
    + admit. (* step in context in assignable *)
  - (* lambda anon *)
    admit.
  - (* hole context, toplevel reduction app *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eapply beta_typed_app;eauto.
  - (* app left *)
    eapply beta_typed_app;eauto.
  - (* app right *)
    eapply beta_typed.
    2: admit. (* context under subst *)
    eapply beta_typed_app;eauto. 
    admit. (* assignable *)
  - (* sigma cons *)
    eapply beta_typed_sigma_cons;eauto.
    admit. (* step in context *)
  - (* sigma anon cons *)
    admit.
  - (* Tuple *)
    eapply beta_typed_tuple;eauto.
    apply list.Forall2_app_inv_l in H as (Ts1&Ts2&HTs1&HTs2&->).
    apply list.Forall2_app_inv_l.
    exists Ts1,Ts2;repeat split;auto.
    inversion HTs2;subst.
    constructor;auto.
    admit. (* nested induction *)
  - (* array *)
    eapply beta_typed_arr;eauto.
    admit. (* step in context *)
  - (* array anon *)
    admit.
  - (* pack *)
    eapply beta_typed.
    2: eapply Ectx_step with (K:=ArrayCtx x0 K T);eauto.
    simpl.
    eapply beta_typed_pack;eauto.
    admit. (* step in context *)
  - (* pack anon *)
    admit.
  - (* hole context, toplevel reduction extract array *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eauto.
  - (* extract array, step array *)
    eapply beta_typed_extract_array;eauto.
  - (* extract array, step index *)
    eapply beta_typed.
    2: admit. (* context under subst *)
    eapply beta_typed_extract_array;eauto.
  - (* hole context, toplevel reduction extract tuple *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eauto.
  - (* extract tuple, step tuple *)
    eapply beta_typed_extract_tuple;eauto.
  - (* extract tuple, step index *)
    eapply beta_typed.
    1: eapply beta_typed_extract_tuple;eauto.
    assert (is_val (Sigma Ts)) by admit.
    eapply Ectx_step with (K:=ExtractRCtx (Sigma Ts) K H0);eauto.


  intros Hty Hstep.
  destruct Hstep as [K eK eK' He He' Hstep].
  induction Hty;inversion K;simpl in *;inversion He;inversion He'.
  all: try eauto.
  - 
Admitted.

Lemma typed_safety e1 e2 A:
  TY ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.



































































(* Lemma fill_typing_decompose K e A:
  TY ∅ ⊢ fill K e : A →
  ∃ B, TY ∅ ⊢ e : B ∧ ectx_typing K B A.
  (* TODO: the fill in of ectx_typing should not just will in e but also in the type A
  e.g. the type of a lambda is the hole => it is also a hole in the type

  TODO: do we need typing contexts for this? 
  
  
  ∅ ⊢ λ (x:𝐍), x+2 : Π (x:𝐍), 𝐍
            ^ e 
  -> ∃ B = *,
  ∅ ⊢ e : *
  but not
  ∀ e',
  ∅ ⊢ e' : *
  ∅ ⊢ λ (x:e'), x+2 : Π (x:𝐍), 𝐍

  even more strict:
  the expression is not even typed for all e'

  TODO: this lemma does not hold
  even the generalization with type contexts does not hold
    (we can not change the type of a lambda independent of the body)
  *)
Proof.
  unfold ectx_typing.
  intros HTy.
  dependent induction HTy.
  all: revert x; dependent inversion K;subst;simpl;try congruence;intros X;subst.
  all: eauto 10.
  - (* pi named *)
    inversion X. edestruct IHHTy1 as (? & ? & ?);eauto.
    eexists;split;[eassumption|].
    intros.
    econstructor.
    all: try eassumption.
    + now apply H4.
    + admit. (* TODO: need Gamma *)
  - (* pi anon *)
    inversion X. edestruct IHHTy1 as (? & ? & ?);eauto.
    eexists;split;[eassumption|].
    subst. intros.
    econstructor.
    all: try eassumption.
    now apply H4.
  - inversion X.
    edestruct IHHTy1 as (? & ? & ?);eauto.
    eexists;split;[eassumption|].
    intros.
    subst.
    eapply typed_lam.
    econstructor.
    all: try eassumption.
    + now apply H4.
    + admit. (* TODO: need Gamma *)

  (* idea: we never go under binder in reduction => no gamma enough *)


  
  - revert x; dependent inversion K;subst;simpl;try congruence.
  dependent induction HTy; dependent inversion K;try congruence.


  (* TODO: hypothesis: the induction is too weak/the context replacement has dependencies on type level *)
  unfold ectx_typing; induction K in A |-*; simpl; inversion 1; subst; eauto.
  all: edestruct IHK as (? & ? & ?); eauto 10.
  - (* we already used IHK and should not need to use it again *)
    exists x. split;[eassumption|].
    intros.
    econstructor.
    + now apply H1.
    + admit.
    + eassumption.
  - admit.
  - eexists;split;[eassumption|].
    intros.
    eapply typed_lam_anon.






  - exists x;split;[assumption|].
    intros e' Hty.
    econstructor;eauto.
    specialize (IHK _ H4).
    destruct IHK as [x' [Hex' Hctx]].
    admit.
  - 

    
  (* - eexists;split;eauto.  intros e' Hty.
    eapply typed_preservation_base_step;eauto. *)
Admitted. *)
  (* unfold ectx_typing; induction K in A |-*; simpl; inversion 1; subst; eauto.
  all: edestruct IHK as (? & ? & ?); eauto.
Qed. *)

Lemma value_characterization e:
  reducible e \/ is_val e.
Proof.
  induction e.
  (* all: 
    (*
    destruct all IH*
    *)
    repeat match goal with
    | H: _ \/ _ |- _ => destruct H
    end. *)
  all: try now (right;econstructor;eauto).
  - admit.
Abort.


(* unused but for completeness/sanity check *)
Lemma value_characterization e:
  ~ reducible e → is_val e.
Proof.
  induction e;simpl;intros Hred.
  all: try econstructor.
  - admit. (* var case => needs closedness *)
  - apply IHe1. contradict Hred.
    destruct Hred as [e1' H].
    inversion H;subst. eexists. 
    eapply Ectx_step with (K:=PiCtx x K e2);eauto.
  - apply IHe1. contradict Hred.
    destruct Hred as [e1' H].
    inversion H;subst. eexists. 
    eapply Ectx_step with (K:=LamCtx x K e2 e3 e4);eauto.
  - exfalso. (* app contradictory *)
    contradict Hred.
    eexists.
    econstructor.
    all: admit.
  - admit. (* sigma *)
  - admit. (* Tuple *)
  - apply IHe1. contradict Hred.
    destruct Hred as [e1' H].
    inversion H;subst. eexists. 
    eapply Ectx_step with (K:=ArrayCtx x K e2);eauto.
  - apply IHe1. contradict Hred.
    destruct Hred as [e1' H].
    inversion H;subst. eexists. 
    eapply Ectx_step with (K:=PackCtx x K e2);eauto.
  - admit. (* extract *)
Abort.


(*
e1 -> e2

subst x e1 e = e \/ exists e', subst x e1 e -> e' (e1 is not necessarily the left-most redex)
*)
Lemma subst_reduction e1 x e:
  reducible e1 →
  subst x e1 e = e ∨ reducible (subst x e1 e).
Proof.
  intros [e2 Hred].
Abort.

(*
  all typed are normalized (values)
  don't go under binders
*)
Inductive normalized_type : expr -> Prop :=
  (* | normalized_val e : is_val e → normalized_type e *)
  (* corresponds to is_val e *)
  | normalized_star : normalized_type Star
  | normalized_box : normalized_type Box
  | normalized_bot : normalized_type Bot
  | normalized_nat : normalized_type Nat
  | normalized_idx : normalized_type Idx 
  | normalized_litnat n : normalized_type (LitNat n)
  | normalized_litidx n i : normalized_type (LitIdx n i)
  | normalized_var x : normalized_type (Var x)
  | normalized_pi x T U : is_val T → normalized_type (Pi x T U)
  | normalized_lam x T ef e U : is_val T → normalized_type (Lam x T ef e U)
  | normalized_app e1 e2 : normalized_type e1 → normalized_type e2 → normalized_type (App e1 e2)
  (* TODO: this is under binder *)
  (* | normalized_sigma Ts : Forall normalized_type Ts → normalized_type (Sigma Ts) *)
  | normalized_sigma_empty : normalized_type (Sigma [])
  | normalized_sigma_cons x T args: normalized_type T → normalized_type (Sigma ((x,T)::args))

  | normalized_tuple es : Forall normalized_type es → normalized_type (Tuple es)
  | normalized_arr x en T : normalized_type en → is_val T → normalized_type (Array x en T)
  | normalized_pack x en e: normalized_type en → normalized_type (Pack x en e)
  | normalized_extract e1 e2 : normalized_type e1 → normalized_type e2 → normalized_type (Extract e1 e2)
.


(* 
for types norm -> is_val
norm -> typed -> is val of the type
in general
is_val -> norm
*)


(*
∅ ⊢ e : A 
e → e'
===========
∅ ⊢ e' : A  



TODO: is this correct?
  λ (x: Idx (1+1)) : 𝐍, if x then 1 else 0 
    : Π (x: Idx (1+1)), 𝐍
  does base step in context
    LamCtx x ... ... 𝐍 (if x then 1 else 0)
  to
  λ (x: Idx 2) : 𝐍, if x then 1 else 0 
            ^
    : Π (x: Idx 2), 𝐍
  
  so the type changes

Lemma typed_preservation e e' A:
  TY ∅ ⊢ e : A →
  contextual_step e e' →
  TY ∅ ⊢ e' : A.
Proof.

TODO: 
  is assuming "value A" safe
  why is this different to assume value e?
*)


(* Hypothesis (typed_beta:
  ∀ Γ e A B,
  TY Γ ⊢ e : A →
  contextual_step B A →
  TY Γ ⊢ e : B
). *)
(*
copy of typing relation with additional beta rule
*)
Reserved Notation "'TY' Γ ⊢' e : A" (at level 74, e, A at next level).
Reserved Notation "'TY' Γ ⊢' A ← e" (at level 74, e, A at next level).
Inductive beta_syn_typed : typing_context → expr → expr → Prop :=
   | beta_typed_star Γ: TY Γ ⊢' Star : Box
   | beta_typed_bot Γ: TY Γ ⊢' Bot : Star
   | beta_typed_nat Γ: TY Γ ⊢' Nat : Star
   | beta_typed_idx Γ: TY Γ ⊢' Idx : (Pi BAnon Nat Star)
   | beta_typed_lit_nat Γ n: TY Γ ⊢' (#n)%E : Nat
   | beta_typed_lit_idx Γ n i: TY Γ ⊢' (LitIdx n i) : (App Idx n)
   | beta_typed_var Γ x A sA: Γ !! x = Some A → TY Γ ⊢' A : sA → TY Γ ⊢' (Var x) : A
   | beta_typed_pi Γ T sT x U sU s: TY Γ ⊢' T : sT → TY (<[x := T]> Γ) ⊢' U : sU → kind_dominance [sT; sU] s → TY Γ ⊢' (Pi (BNamed x) T U) : s
   | beta_typed_pi_anon Γ T sT U sU s: TY Γ ⊢' T : sT → TY Γ ⊢' U : sU → kind_dominance [sT; sU] s → TY Γ ⊢' (Pi BAnon T U) : s
   | beta_typed_lam Γ x T ef U e sT sU: TY Γ ⊢' T : sT → TY (<[x := T]> Γ) ⊢' U : sU → TY (<[x := T]> Γ) ⊢' ef : Bool → beta_type_assignable (<[x := T]> Γ) U e → TY Γ ⊢' (Lam (BNamed x) T ef U e) : (Pi (BNamed x) T U)
   | beta_typed_lam_anon Γ T ef U e sT sU: TY Γ ⊢' T : sT → TY Γ ⊢' U : sU → TY Γ ⊢' ef : Bool → beta_type_assignable Γ T e → TY Γ ⊢' (Lam BAnon T ef U e) : (Pi BAnon T U)
   | beta_typed_app Γ e eT x T U: TY Γ ⊢' e : (Pi x T U) → beta_type_assignable Γ T eT → TY Γ ⊢' (App e eT) : (subst' x eT U)
   | beta_typed_sigma_empty Γ: TY Γ ⊢' Sigma [] : Star
   | beta_typed_sigma_cons Γ x T s xs s' s'': TY Γ ⊢' T : s → TY (<[x := T]> Γ) ⊢' Sigma xs : s' → kind_dominance [s; s'] s'' → TY Γ ⊢' (Sigma ((BNamed x, T)::xs)) : s''
   | beta_typed_sigma_cons_anon Γ T s xs s' s'': TY Γ ⊢' T : s → TY Γ ⊢' Sigma xs : s' → kind_dominance [s; s'] s'' → TY Γ ⊢' (Sigma ((BAnon, T)::xs)) : s''
   | beta_typed_tuple Γ es Ts T: Forall2 (syn_typed Γ) es Ts → T = Sigma (map (fun T => (BAnon, T)) Ts) -> TY Γ ⊢' (Tuple es) : T
   | beta_typed_arr Γ x en T s: sort s → TY Γ ⊢' en : Nat → TY (<[x := App Idx en]> Γ) ⊢' T : s → TY Γ ⊢' (Array (BNamed x) en T) : s
   | beta_typed_arr_anon Γ en T s: sort s → TY Γ ⊢' en : Nat → TY Γ ⊢' T : s → TY Γ ⊢' (Array BAnon en T) : s
   | beta_typed_pack Γ x en e T: TY Γ ⊢' en : Nat → TY (<[x := App Idx en]> Γ) ⊢' e : T → TY Γ ⊢' (Pack (BNamed x) en e) : (Array (BNamed x) en T)
   | beta_typed_pack_anon Γ en e T: TY Γ ⊢' en : Nat → TY Γ ⊢' e : T → TY Γ ⊢' (Pack BAnon en e) : (Array BAnon en T)
   | beta_typed_extract_array Γ e ei en T x: TY Γ ⊢' e : (Array x en T) → TY Γ ⊢' ei : (App Idx en) → TY Γ ⊢' (Extract e ei) : (subst' x ei T)
   | beta_typed_extract_tuple Γ e ei Ts Ts' T n s U: TY Γ ⊢' e : (Sigma Ts) → n = length Ts → TY Γ ⊢' ei : (App Idx n) → Ts' = Ts -> T = Sigma Ts' -> TY Γ ⊢' T : s -> U = Extract T ei -> TY Γ ⊢' (Extract e ei) : U
   | beta_typed Γ A B e:
      TY Γ ⊢' e : A →
      contextual_step B A →
      TY Γ ⊢' e : B
   (* | beta_typed_rev Γ A B e:
      TY Γ ⊢' e : A →
      contextual_step A B →
      TY Γ ⊢' e : B *)

with beta_type_assignable : typing_context -> expr -> expr -> Prop :=
  | beta_assignable_typed Γ e T:
      TY Γ ⊢' e : T ->
      beta_type_assignable Γ T e
  | beta_assignable_sigma Γ Ts e:
      beta_type_assignable Γ (Sigma Ts) e
where "'TY' Γ ⊢' e : A" := (beta_syn_typed Γ e%E A%E).
#[export] Hint Constructors beta_syn_typed : core.


Lemma typed_beta_typed Γ e A:
  TY Γ ⊢ e : A →
  TY Γ ⊢' e : A.
Proof.
  induction 1;eauto.
Qed.


(* Lemma beta_typed_typed Γ e A:
  TY ∅ ⊢' e : A →
  normalized_type e →
  TY ∅ ⊢ e : A.
Proof.
  intros H1 H2.
  dependent induction H1;eauto.
  - *)


(* Inductive normalize : expr -> expr -> Prop :=
  | normalize_ *)




(*
only allow beta conversion for types at toplevel (empty context) ?
=> would avoid deeper conversion issues
(does normalization go under binders?)

normalization from bottom up => inside out

*)

Variable normalized : expr → Prop.

Print typing_context.
Definition Forall_gmap {X} (P: string → X → Prop) (m: gmap string X) :=
  forall x T, m !! x = Some T → P x T.
Definition normalized_context (Γ: typing_context) :=
  Forall_gmap (fun _ => normalized) Γ.

Lemma unfold_norm_context_cons x T Γ:
  (* normalized_context (<[x:=T]> Γ) ↔ normalized T ∧ normalized_context Γ. *)
  normalized T → normalized_context Γ → normalized_context (<[x:=T]> Γ).
Proof.
  intros H1 H2 x' T' H3.
  destruct (decide (x = x')).
  - subst. rewrite lookup_insert in H3. inversion H3;subst. assumption.
  - rewrite lookup_insert_ne in H3;auto.
    unfold normalized_context, Forall_gmap in H2.
    eapply H2;eassumption.
Qed.

#[export]
Hint Resolve unfold_norm_context_cons : core.

Lemma beta_typed_typed Γ e A:
  TY Γ ⊢' e : A →
  (* everything in context normalized *)
  (* (forall x T, Γ !! x = Some T → normalized T) → *)
  normalized_context Γ →
  normalized e →
  TY Γ ⊢ e : A.
Proof.
  intros H1 HΓ Hnorm.
  induction H1;eauto.
  (*
  - (* var *)
    econstructor;eauto. apply IHbeta_syn_typed.
    admit. 
    (* 
      know x is normalized but want the type of x (A) is normalized
      solution: context normalized 
    *)
  *)
  - (* pi named *)
    (* inversion H2;subst. *)
    econstructor;eauto.
    + apply IHbeta_syn_typed1;eauto. all: admit. 
      (* 
        norm T 
        => follows from norm (Pi x T U)
      *)
    + apply IHbeta_syn_typed2;eauto. 
      * (* norm context under binder *)
        apply unfold_norm_context_cons;eauto.
        admit. (* norm T => rest is assumption *)
      * admit. (* norm U *)
        (*
          norm U
          => follows from norm (Pi x T U)
        *)
  - (* pi anon *)
    admit.
  - (* lambda named *)
    econstructor;eauto.
    (* we have norm (λ (x:T) @ef : U, e) *)
    + apply IHbeta_syn_typed1;eauto. admit. (* norm T *)
    + apply IHbeta_syn_typed2;eauto. all: admit. (* norm U *)
    + apply IHbeta_syn_typed3;eauto. all: admit. (* norm ef *)
    + admit. (* assignable mutual induction *)
  - (* lambda anon *)
    admit.
  - (* app *)
    econstructor;eauto.
    2: admit. (* assignable mutual induction *)
    apply IHbeta_syn_typed. assumption.
    admit. (* norm (e eT) => norm e *)
  - (* sigma cons *)
    admit. (* TODO *)
  - (* sigma cons anon *)
    admit.
  - (* array *)
    admit. (* TODO *)
  - (* array anon *)
    admit.
  - (* pack *)
    admit. (* TODO *)
  - (* pack anon *)
    admit.
  - (* extract array *)
    admit. (* TODO *)
  - (* extract tuple *)
    admit.
  - (* beta *)

    admit. (* TODO *)
    (* 
  - (* rev beta *)
    admit.
    *)
Abort.


Lemma typed_preservation_base_step_beta e e' A:
  TY ∅ ⊢' e : A →
  base_step e e' →
  TY ∅ ⊢' e' : A.
Admitted.


Lemma typed_preservation e e' A:
  TY ∅ ⊢' e : A →
  contextual_step e e' →
  TY ∅ ⊢' e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].

  dependent induction Hty;eauto.
  all: destruct K;simpl in *;try congruence;subst.
  all: try now inversion Hstep.
  all: try inversion x;subst.
  - (* pi named *)
    eapply beta_typed_pi;eauto.
    admit. (* step in context *)
  - (* pi anon *)
    admit.
  - (* lambda named *)
    eapply beta_typed.
    2: eapply Ectx_step with (K:=PiCtx x0 K U0);eauto.
    simpl.
    eapply beta_typed_lam;eauto.
    + admit. (* step in context *)
    + admit. (* step in context *)
    + admit. (* step in context in assignable *)
  - (* lambda anon *)
    admit.
  - (* hole context, toplevel reduction app *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eapply beta_typed_app;eauto.
  - (* app left *)
    eapply beta_typed_app;eauto.
  - (* app right *)
    eapply beta_typed.
    2: admit. (* context under subst *)
    eapply beta_typed_app;eauto. 
    admit. (* assignable *)
  - (* sigma cons *)
    eapply beta_typed_sigma_cons;eauto.
    admit. (* step in context *)
  - (* sigma anon cons *)
    admit.
  - (* Tuple *)
    eapply beta_typed_tuple;eauto.
    apply list.Forall2_app_inv_l in H as (Ts1&Ts2&HTs1&HTs2&->).
    apply list.Forall2_app_inv_l.
    exists Ts1,Ts2;repeat split;auto.
    inversion HTs2;subst.
    constructor;auto.
    admit. (* nested induction *)
  - (* array *)
    eapply beta_typed_arr;eauto.
    admit. (* step in context *)
  - (* array anon *)
    admit.
  - (* pack *)
    eapply beta_typed.
    2: eapply Ectx_step with (K:=ArrayCtx x0 K T);eauto.
    simpl.
    eapply beta_typed_pack;eauto.
    admit. (* step in context *)
  - (* pack anon *)
    admit.
  - (* hole context, toplevel reduction extract array *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eauto.
  - (* extract array, step array *)
    eapply beta_typed_extract_array;eauto.
  - (* extract array, step index *)
    eapply beta_typed.
    2: admit. (* context under subst *)
    eapply beta_typed_extract_array;eauto.
  - (* hole context, toplevel reduction extract tuple *)
    eapply typed_preservation_base_step_beta.
    2: eassumption.
    eauto.
  - (* extract tuple, step tuple *)
    eapply beta_typed_extract_tuple;eauto.
  - (* extract tuple, step index *)
    eapply beta_typed.
    1: eapply beta_typed_extract_tuple;eauto.
    assert (is_val (Sigma Ts)) by admit.
    eapply Ectx_step with (K:=ExtractRCtx (Sigma Ts) K H0);eauto.
Admitted.










  induction K in A, Hty |- *;simpl in *.
  1: {
    admit.
    (* eapply typed_preservation_base_step. 
    all: eassumption. *)
  }

  - inversion Hty;subst;eauto.
    + eapply beta_typed_pi;eauto.
      admit. (* step in context *)
    + eapply beta_typed_pi;eauto.
      admit. (* same *)



  all: inversion Hty;subst.
  all: eauto.
  - (* pi named *)
    eapply beta_typed_pi;eauto.
    admit. (* step in context *)
  - (* pi anon *)
    admit. (* same *)
  - (* lam named *)
    eapply beta_typed.
    2: eapply Ectx_step with (K:=PiCtx x0 K U);eauto.
    eapply typed_lam;eauto.
    + admit. (* step in context *)
    + admit. (* step in context *)
    + admit. (* step in context in assignable *)
  - (* lambda anon *)
    admit. (* same *)
  - (* app left *)
    eapply typed_app;eauto.
  - (* app right *)
    eapply typed_beta.
    2: admit. (* context under subst *)
    eapply typed_app;eauto. 
    admit. (* assignable *)
  - (* sigma cons *)
    eapply typed_sigma_cons;eauto.
    admit. (* step in context *)
  - (* sigma anon cons *)
    admit. (* same *)
  - (* tuple *)
    eapply typed_tuple;eauto.
    apply list.Forall2_app_inv_l in H1 as (Ts1&Ts2&HTs1&HTs2&->).
    apply list.Forall2_app_inv_l.
    exists Ts1,Ts2;repeat split;auto.
    inversion HTs2;subst.
    constructor;auto.
  - (* array *)
    eapply typed_arr;eauto.
    admit. (* step in context *)
  - (* array anon *)
    admit. (* same *)
  - (* pack *)
    eapply typed_beta.
    2: eapply Ectx_step with (K:=ArrayCtx x0 K T);eauto.
    eapply typed_pack;eauto.
    admit. (* step in context *)
  - (* pack anon *)
    admit. (* same *)
  - (* extract array, step array *)
    eapply typed_extract_array;eauto.
  - (* extract tuple, step tuple *)
    eapply typed_extract_tuple;eauto.
  - (* extract array, step index *)
    eapply typed_beta.
    2: admit. (* context under subst *)
    eapply typed_extract_array;eauto.
  - (* extract tuple, step index *)
  (* is_val e and e : Sigma Ts *)
    assert (is_val (Sigma Ts)) by admit.
    eapply typed_beta.
    2: {
      eapply Ectx_step with (K:=ExtractRCtx (Sigma Ts) K H0);eauto.
    }
    eapply typed_extract_tuple;eauto.
Admitted.





















Lemma typed_preservation e e' A:
  TY ∅ ⊢ e : A →
  contextual_step e e' →
  (* exists B, TY ∅ ⊢ e' : B /\ rtc contextual_step A B. *)
  exists B, TY ∅ ⊢ e' : B /\ (A=B \/ contextual_step A B).
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].

  induction K in A, Hty |- *;simpl in *.
  1: {
    eexists;split;[|now left].
    eapply typed_preservation_base_step. 
    all: eassumption.
  }
  all: inversion Hty;subst.
  - (* pi named *)
    eexists;split;[|now left].
    eapply typed_pi;eauto.
    + admit. (* IH *)
    + admit. (* TODO: reduction step in context *)
  - (* pi anon *)
    admit.
  - (* lam named *)
    exists (Pi x0 (fill K e2) U);split.
    + eapply typed_lam;eauto.
      * admit. (* IH *)
      * admit. (* reduction step in context *)
      * admit. (* reduction step in context *)
      * admit. (* mutual induction assignable *)
    + right.
      eapply Ectx_step with (K:=PiCtx x0 K U);eauto.
  - (* lam anon *)
    admit.
  - (* app left *)
    destruct (IHK _ H2) as (B&He2_B&[<-|HA_B]).
    + eexists;split.
      * eapply typed_app;eauto.
      * now left.
    + 

      clear IHK.
      eexists;split.
      * eapply typed_app;eauto.
    
    
    
    
    
    eexists;split.
      * eapply typed_app;eauto.
        inversion HA_B;subst.
        destruct K0;simpl in *;try congruence;subst.
        -- (* hole context *)
          inversion H1.
        -- (* PiCtx *)
          apply He2_B.

    + eapply typed_app;eauto.
      inversion He2_B;subst;eauto.
    (* eexists;split;[|constructor]. *)
    eapply typed_app;eauto.
    admit. (* IH *)


    eexists;split;[|constructor].
    eapply typed_app;eauto.
    admit. (* IH *)
  - 





Lemma typed_preservation e e' A:
  (* is_val A → *)
  normalized_type e →
  TY ∅ ⊢ e : A →
  contextual_step e e' →
  TY ∅ ⊢ e' : A.
Proof.
  intros Hval Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].

  induction K in A, Hval, Hty |- *;simpl in *.
  1: eapply typed_preservation_base_step;eassumption.
  all: inversion Hty;subst.
  - (* pi named *)
    eapply typed_pi;try eassumption.
    + apply IHK;eauto. 
      inversion Hval;subst.
      admit. (* is_val is easy *)
    + admit. (* TODO: reduction step in context (strengthen the goal) *)
  - (* pi anon *)
    eapply typed_pi_anon;try eassumption.
    apply IHK;eauto. admit. (* is_val is easy *)
  - (* lambda named *)
    exfalso.
    eapply values_dont_reduce;eauto.
    1: {
      inversion Hval;subst.
      eapply PiV.
      apply H0.
    }
    eexists. eapply Ectx_step with (K:=PiCtx x0 K U);eauto.
    (*
    (* TODO: allow beta step(s) at type *)
    (* state later that is_val A implies that beta equiv terms are equal *)
    (* change Pi x0 (fill K e1) to (Pi x0 (fill K e2)) *)
    (* enough (TY ∅ ⊢ (λ: (x0 : fill K e2) @f : U, e) : Pi x0 (fill K e2) U) by admit. *)
    enough (TY ∅ ⊢ (Lam x0 (fill K e2) f U e) : Pi x0 (fill K e2) U) by admit.
    eapply typed_lam.
    + apply IHK;eassumption.
    + admit. (* TODO: reduction step in context (strengthen the goal) *)
    + admit. (* TODO: reduction step in context (strengthen the goal) *)
    + admit. (* TODO: assignable induction *)
    *)
  - (* lambda anon *)
    enough (TY ∅ ⊢ (Lam BAnon (fill K e2) f U e) : Pi BAnon (fill K e2) U) by admit.
    eapply typed_lam_anon;eauto.
    apply IHK.
    1: eassumption.
    + inversion Hval;subst.
      admit. (* TODO: is val *)
    + admit. (* TODO: assignable induction *)
  - (* app left context *)
    eapply typed_app.
    + apply IHK;eauto. 
      inversion Hval;subst.
      assumption.
    (* admit.  *)
    (* TODO: 
      here, we need that the type of e1 (Pi x T U) is also a value for induction
      however, we only know that U is a value
      => we want inner types as values
      normalization should also guarantee this however
    *)
    + assumption.
  - (* app right context *)
    inversion Hval;subst.

    exfalso.
    eapply values_dont_reduce. 
    1: {
      inversion Hval;subst.
      admit.
    }
    eexists. admit. (* TODO: reduction under subst *)
    (*
    (* again apply reduction step in goal => replace e1 with e2 *)
    enough (TY ∅ ⊢ e0 (fill K e2) : subst' x (fill K e2) U) by admit.
    eapply typed_app.
    + eassumption.
    + admit. (* TODO: assignable induction *)
    *)
  - (* sigma cons named *)
    eapply typed_sigma_cons;eauto.
    + apply IHK;eauto. 
      inversion Hval;subst.
      assumption.
      (* admit.  *)
    + admit. (* TODO: reduction in context *)
  - (* sigma cons anon *)
    eapply typed_sigma_cons_anon;eauto.
    apply IHK;eauto. 
    inversion Hval;subst.
    assumption.
    (* admit. (* simple is val *) *)
  - (* tuple *)
    eapply typed_tuple;eauto.
    apply list.Forall2_app_inv_l in H1 as (Ts1&Ts2&HTs1&HTs2&HTs).
    apply list.Forall2_app_inv_l.
    inversion HTs2;subst.
    do 2 eexists;repeat split;eauto.
    constructor;eauto.
    apply IHK;eauto.
    inversion Hval;subst.
    apply Forall_app in H1 as [].
    now inversion H1;subst.
    (* admit. (* inner is val of unreduced head type *) *)
  - (* array *)
    eapply typed_arr;eauto.
    + apply IHK;eauto. 
      inversion Hval;subst. assumption.
    + admit. (* TODO: reduction in context *)
  - (* array anon *)
    eapply typed_arr_anon;eauto.
    apply IHK;eauto. 
    inversion Hval;subst. assumption.
  - (* pack *)
    exfalso.
    eapply values_dont_reduce. 
    2: {
      eexists. eapply Ectx_step with (K:=ArrayCtx x0 K T);eauto.
    }
    inversion Hval;subst.
    simpl.
    constructor.
    admit.
    (*
    (* reduction in type *)
    enough (TY ∅ ⊢ Pack x0 (fill K e2) e : Array x0 (fill K e2) T) by admit.  
    eapply typed_pack;eauto.
    admit. (* TODO: reduction in context *)
    *)
  - (* pack anon *)
    exfalso.
    eapply values_dont_reduce. 
    2: {eexists. eapply Ectx_step with (K:=ArrayCtx BAnon K T);eauto. }
    simpl. constructor.
    inversion Hval;subst.
    admit.
    (* enough (TY ∅ ⊢ Pack BAnon (fill K e2) e : Array BAnon (fill K e2) T) by admit.  
    eapply typed_pack_anon;eauto. *)
  - (* extract array left *)
    eapply typed_extract_array;eauto.
    apply IHK;eauto. 
    inversion Hval;subst.
    assumption.
  - (* extract sigma left *)
    inversion Hval;subst.
    econstructor;eauto.
    (*
    eapply typed_extract_tuple;eauto.
    apply IHK;eauto. admit. (* sigma is value *)
    *) 
  - (* extract array right *)
    (* eapply typed_extract_array;eauto. *)

    exfalso.
    eapply values_dont_reduce. 
    all: admit. (* e1 in index takes a step *)
    (* 1: apply Hval.
    eexists. admit.  *)
    (* TODO: reduction under subst *)
    (* replace (fill K e1) with (fill K e2) by admit.
    eapply typed_extract_array;eauto. *)
  - (* extract sigma right *)
    inversion Hval;subst.
    econstructor;eauto.
    (* replace (fill K e1) with (fill K e2) by admit.
    eapply typed_extract_tuple;eauto. *)





  (* revert e2 Hstep .
  dependent induction Hty;intros e2 Hstep;destruct K;simpl in *.
  (* inversion K;subst;simpl in *;try congruence. *)
  all: try congruence.
  (* all: inversion Hstep;subst.
  all: try congruence. *)
  all: try now (inversion Hstep;subst;try congruence).
  - inversion x;subst.
  - inversion Hstep;subst;try congruence.
  - inversion Hstep;subst;try congruence.
  -  *)

  (* induction K in e1,e2,Hstep,Hty |- *;simpl in *. *)
  induction K in A, Hval, Hty |- *;simpl in *.
  - admit.
  - (* Pi *)
    inversion Hty;subst.
    + econstructor;eauto.
      all: admit. (* e2 instead of e1 in context *)
    + econstructor;eauto.
      all: admit.
    (* TODO: this reduction in type is impossible (is it?)
      otherwise, we would have a reduction in the type

      not true: the type is a kind (star/box) which is a value

    *)
  - 

  inversion Hstep;subst.
  - 

  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply typed_preservation_base_step.
Qed.

Lemma typed_safety e1 e2 A:
  TY ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.


(*
(some subst lemmas and context lemmas)

Preservation over base step (Subject reduction)
Preservation over context step (corollary)

possibly allow reduction in type context

Together type safety (corollary)
*)




































(**
================================================================================================
======================= Here be dragons ========================================================
================================================================================================
Old development for guideline ahead, erase while going forward.
*)






(** *** Lemmas about [type_wf] *)
Lemma type_wf_mono n m A:
  type_wf n A → n ≤ m → type_wf m A.
Proof.
  induction 1 in m |-*; eauto with lia.
Qed.

Lemma type_wf_rename n A δ:
  type_wf n A →
  (∀ i j, i < j → δ i < δ j) →
  type_wf (δ n) (rename δ A).
Proof.
  induction 1 in δ |-*; intros Hmon; simpl; eauto.
  all: econstructor; eapply type_wf_mono; first eapply IHtype_wf; last done.
  all: intros i j Hlt; destruct i, j; simpl; try lia.
  all: rewrite -Nat.succ_lt_mono; eapply Hmon; lia.
Qed.

(** [A.[σ]], i.e. [A] with the substitution [σ] applied to it, is well-formed under [m] if
   [A] is well-formed under [n] and all the things we substitute up to [n] are well-formed under [m].
 *)
Lemma type_wf_subst n m A σ:
  type_wf n A →
  (∀ x, x < n → type_wf m (σ x)) →
  type_wf m A.[σ].
Proof.
  induction 1 in m, σ |-*; intros Hsub; simpl; eauto.
  + econstructor; eapply IHtype_wf.
    intros [|x]; rewrite /up //=.
    - econstructor. lia.
    - intros Hlt % Nat.succ_lt_mono. eapply type_wf_rename; eauto.
      intros i j Hlt'; simpl; lia.
  + econstructor; eapply IHtype_wf.
    intros [|x]; rewrite /up //=.
    - econstructor. lia.
    - intros Hlt % Nat.succ_lt_mono. eapply type_wf_rename; eauto.
      intros i j Hlt'; simpl; lia.
Qed.

Lemma type_wf_single_subst n A B: type_wf n B → type_wf (S n) A → type_wf n A.[B/].
Proof.
  intros HB HA. eapply type_wf_subst; first done.
  intros [|x]; simpl; eauto.
  intros ?; econstructor. lia.
Qed.

(** We lift [type_wf] to well-formedness of contexts *)
Definition ctx_wf n Γ := (∀ x A, Γ !! x = Some A → type_wf n A).

Lemma ctx_wf_empty n : ctx_wf n ∅.
Proof. rewrite /ctx_wf. set_solver. Qed.

Lemma ctx_wf_insert n x Γ A: ctx_wf n Γ → type_wf n A → ctx_wf n (<[x := A]> Γ).
Proof. intros H1 H2 y B. rewrite lookup_insert_Some. naive_solver. Qed.

Lemma ctx_wf_up n Γ:
  ctx_wf n Γ → ctx_wf (S n) (⤉Γ).
Proof.
  intros Hwf x A; rewrite lookup_fmap.
  intros (B & Hlook & ->) % fmap_Some.
  asimpl. eapply type_wf_subst; first eauto.
  intros y Hlt. simpl. econstructor. lia.
Qed.

#[global]
Hint Resolve ctx_wf_empty ctx_wf_insert ctx_wf_up : core.

(** Well-typed terms at [A] under a well-formed context have well-formed types [A].*)
Lemma syn_typed_wf n Γ e A:
  ctx_wf n Γ →
  TY n; Γ ⊢ e : A →
  type_wf n A.
Proof.
  intros Hwf; induction 1 as [ | n Γ x e A B Hty IH Hwfty | | n Γ e A Hty IH | n Γ A B e Hty IH Hwfty | n Γ A B e Hwfty Hty IH| | |  | | | n Γ e1 e2 A B HtyA IHA HtyB IHB | n Γ e1 e2 op A B C Hop HtyA IHA HtyB IHB | n Γ e op A B Hop H IH | n Γ e1 e2 A B HtyA IHA HtyB IHB | n Γ e A B Hty IH | n Γ e A B Hty IH | n Γ e A B Hwfty Hty IH | n Γ e A B Hwfty Hty IH| n Γ e e1 e2 A B C Htye IHe Htye1 IHe1 Htye2 IHe2 ]; eauto.
  - eapply type_wf_single_subst; first done.
    specialize (IH Hwf) as Hwf'.
    by inversion Hwf'.
  - specialize (IHA Hwf) as Hwf'.
    by inversion Hwf'; subst.
  - inversion Hop; subst; eauto.
  - inversion Hop; subst; eauto.
  - specialize (IH Hwf) as Hwf'. by inversion Hwf'; subst.
  - specialize (IH Hwf) as Hwf'. by inversion Hwf'; subst.
  - specialize (IHe1 Hwf) as Hwf''. by inversion Hwf''; subst.
Qed.

Lemma renaming_inclusion Γ Δ : Γ ⊆ Δ → ⤉Γ ⊆ ⤉Δ.
Proof.
  eapply map_fmap_mono.
Qed.

(* Lemma typed_weakening n m Γ Δ e A:
  TY n; Γ ⊢ e : A →
  Γ ⊆ Δ →
  n ≤ m →
  TY m; Δ ⊢ e : A.
Proof.
Qed. *)

Lemma type_wf_subst_dom σ τ n A:
  type_wf n A →
  (∀ m, m < n → σ m = τ m) →
  A.[σ] = A.[τ].
Proof.
  induction 1 in σ, τ |-*; simpl; eauto.
  - (* tforall *)
    intros Heq; asimpl. f_equal.
    eapply IHtype_wf; intros [|m]; rewrite /up; simpl; first done.
    intros Hlt. f_equal. eapply Heq. lia.
  - (* texists *)
    intros Heq; asimpl. f_equal.
    eapply IHtype_wf. intros [ | m]; rewrite /up; simpl; first done.
    intros Hlt. f_equal. apply Heq. lia.
  - (* fun *) intros ?. f_equal; eauto.
  - (* prod *) intros ?. f_equal; eauto.
  - (* sum *) intros ?. f_equal; eauto.
Qed.

Lemma type_wf_closed A σ:
  type_wf 0 A →
  A.[σ] = A.
Proof.
  intros Hwf; erewrite (type_wf_subst_dom _ (ids) 0).
  - by asimpl.
  - done.
  - intros ??; lia.
Qed.

(** Typing inversion lemmas *)
(* Lemma var_inversion Γ n (x: string) A: TY n; Γ ⊢ x : A → Γ !! x = Some A.
Proof. inversion 1; subst; auto. Qed.

Lemma lam_inversion n Γ (x: string) e C:
  TY n; Γ ⊢ (λ: x, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧ TY n; <[x:=A]> Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma lam_anon_inversion n Γ e C:
  TY n; Γ ⊢ (λ: <>, e) : C →
  ∃ A B, C = (A → B)%ty ∧ type_wf n A ∧ TY n; Γ ⊢ e : B.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma app_inversion n Γ e1 e2 B:
  TY n; Γ ⊢ e1 e2 : B →
  ∃ A, TY n; Γ ⊢ e1 : (A → B) ∧ TY n; Γ ⊢ e2 : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma if_inversion n Γ e0 e1 e2 B:
  TY n; Γ ⊢ If e0 e1 e2 : B →
  TY n; Γ ⊢ e0 : Bool ∧ TY n; Γ ⊢ e1 : B ∧ TY n; Γ ⊢ e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma binop_inversion n Γ op e1 e2 B:
  TY n; Γ ⊢ BinOp op e1 e2 : B →
  ∃ A1 A2, bin_op_typed op A1 A2 B ∧ TY n; Γ ⊢ e1 : A1 ∧ TY n; Γ ⊢ e2 : A2.
Proof. inversion 1; subst; eauto. Qed.

Lemma unop_inversion n Γ op e B:
  TY n; Γ ⊢ UnOp op e : B →
  ∃ A, un_op_typed op A B ∧ TY n; Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_app_inversion n Γ e B:
  TY n; Γ ⊢ e <> : B →
  ∃ A C, B = A.[C/] ∧ type_wf n C ∧ TY n; Γ ⊢ e : (∀: A).
Proof. inversion 1; subst; eauto. Qed.

Lemma type_lam_inversion n Γ e B:
  TY n; Γ ⊢ (Λ,e) : B →
  ∃ A, B = (∀: A)%ty ∧ TY (S n); ⤉Γ ⊢ e : A.
Proof. inversion 1; subst; eauto. Qed.

Lemma type_pack_inversion n Γ e B :
  TY n; Γ ⊢ (pack e) : B →
  ∃ A C, B = (∃: A)%ty ∧ TY n; Γ ⊢ e : (A.[C/])%ty ∧ type_wf n C ∧ type_wf (S n) A.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma type_unpack_inversion n Γ e e' x B :
  TY n; Γ ⊢ (unpack e as x in e') : B →
  ∃ A x', x = BNamed x' ∧ type_wf n B ∧ TY n; Γ ⊢ e : (∃: A) ∧ TY S n; <[x' := A]> (⤉Γ) ⊢ e' : (B.[ren (+1)]).
Proof. inversion 1; subst; eauto 10. Qed.

Lemma pair_inversion n Γ e1 e2 C :
  TY n; Γ ⊢ (e1, e2) : C →
  ∃ A B, C = (A × B)%ty ∧ TY n; Γ ⊢ e1 : A ∧ TY n; Γ ⊢ e2 : B.
Proof. inversion 1; subst; eauto. Qed.

Lemma fst_inversion n Γ e A :
  TY n; Γ ⊢ Fst e : A →
  ∃ B, TY n; Γ ⊢ e : A × B.
Proof. inversion 1; subst; eauto. Qed.

Lemma snd_inversion n Γ e B :
  TY n; Γ ⊢ Snd e : B →
  ∃ A, TY n; Γ ⊢ e : A × B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injl_inversion n Γ e C :
  TY n; Γ ⊢ InjL e : C →
  ∃ A B, C = (A + B)%ty ∧ TY n; Γ ⊢ e : A ∧ type_wf n B.
Proof. inversion 1; subst; eauto. Qed.

Lemma injr_inversion n Γ e C :
  TY n; Γ ⊢ InjR e : C →
  ∃ A B, C = (A + B)%ty ∧ TY n; Γ ⊢ e : B ∧ type_wf n A.
Proof. inversion 1; subst; eauto. Qed.

Lemma case_inversion n Γ e e1 e2 A :
  TY n; Γ ⊢ Case e e1 e2 : A →
  ∃ B C, TY n; Γ ⊢ e : B + C ∧ TY n; Γ ⊢ e1 : (B → A) ∧ TY n; Γ ⊢ e2 : (C → A).
Proof. inversion 1; subst; eauto. Qed. *)


Lemma typed_substitutivity n e e' Γ (x: string) A B :
  TY 0; ∅ ⊢ e' : A →
  TY n; (<[x := A]> Γ) ⊢ e : B →
  TY n; Γ ⊢ lang.subst x e' e : B.
Proof.
  intros He'. revert n B Γ; induction e as [| y | y | | | | | | | | | | | | | | ]; intros n B Γ; simpl.
  - inversion 1; subst; auto.
  - intros Hp % var_inversion.
    destruct (decide (x = y)).
    + subst. rewrite lookup_insert in Hp. injection Hp as ->.
      eapply typed_weakening; [done| |lia]. apply map_empty_subseteq.
    + rewrite lookup_insert_ne in Hp; last done. auto.
  - destruct y as [ | y].
    { intros (A' & C & -> & Hwf & Hty) % lam_anon_inversion.
      econstructor; last done. destruct decide as [Heq|].
      + congruence.
      + eauto.
    }
    intros (A' & C & -> & Hwf & Hty) % lam_inversion.
    econstructor; last done. destruct decide as [Heq|].
    + injection Heq as [= ->]. by rewrite insert_insert in Hty.
    + rewrite insert_commute in Hty; last naive_solver. eauto.
  - intros (C & Hty1 & Hty2) % app_inversion. eauto.
  - intros (? & Hop & H1) % unop_inversion.
    destruct op; inversion Hop; subst; eauto.
  - intros (? & ? & Hop & H1 & H2) % binop_inversion.
    destruct op; inversion Hop; subst; eauto.
  - intros (H1 & H2 & H3)%if_inversion. naive_solver.
  - intros (C & D & -> & Hwf & Hty) % type_app_inversion. eauto.
  - intros (C & -> & Hty)%type_lam_inversion. econstructor.
    eapply IHe. revert Hty. rewrite fmap_insert.
    eapply syn_typed_wf in He'; last by naive_solver.
    rewrite type_wf_closed; eauto.
  - intros (C & D & -> & Hty & Hwf1 & Hwf2)%type_pack_inversion.
    econstructor; [done..|]. apply IHe. done.
  - intros (C & x' & -> & Hwf & Hty1 & Hty2)%type_unpack_inversion.
    econstructor; first done.
    + eapply IHe1. done.
    + destruct decide as [Heq | ].
      * injection Heq as [= ->]. by rewrite fmap_insert insert_insert in Hty2.
      * rewrite fmap_insert in Hty2. rewrite insert_commute in Hty2; last naive_solver.
        eapply IHe2. rewrite type_wf_closed in Hty2; first done.
        eapply syn_typed_wf; last apply He'. done.
  - intros (? & ? & -> & ? & ?) % pair_inversion. eauto.
  - intros (? & ?)%fst_inversion. eauto.
  - intros (? & ?)%snd_inversion. eauto.
  - intros (? & ? & -> & ? & ?)%injl_inversion. eauto.
  - intros (? & ? & -> & ? & ?)%injr_inversion. eauto.
  - intros (? & ? & ? & ? & ?)%case_inversion. eauto.
Qed.

(** Canonical values *)
Lemma canonical_values_arr n Γ e A B:
  TY n; Γ ⊢ e : (A → B) →
  is_val e →
  ∃ x e', e = (λ: x, e')%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_forall n Γ e A:
  TY n; Γ ⊢ e : (∀: A)%ty →
  is_val e →
  ∃ e', e = (Λ, e')%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_exists n Γ e A :
  TY n; Γ ⊢ e : (∃: A) →
  is_val e →
  ∃ e', e = (pack e')%E.
Proof. inversion 1; simpl; naive_solver. Qed.

Lemma canonical_values_int n Γ e:
  TY n; Γ ⊢ e : Int →
  is_val e →
  ∃ n: Z, e = (#n)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_bool n Γ e:
  TY n; Γ ⊢ e : Bool →
  is_val e →
  ∃ b: bool, e = (#b)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_unit n Γ e:
  TY n; Γ ⊢ e : Unit →
  is_val e →
  e = (#LitUnit)%E.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_prod n Γ e A B :
  TY n; Γ ⊢ e : A × B →
  is_val e →
  ∃ e1 e2, e = (e1, e2)%E ∧ is_val e1 ∧ is_val e2.
Proof.
  inversion 1; simpl; naive_solver.
Qed.

Lemma canonical_values_sum n Γ e A B :
  TY n; Γ ⊢ e : A + B →
  is_val e →
  (∃ e', e = InjL e' ∧ is_val e') ∨ (∃ e', e = InjR e' ∧ is_val e').
Proof.
  inversion 1; simpl; naive_solver.
Qed.

(** Progress *)
Lemma typed_progress e A:
  TY 0; ∅ ⊢ e : A → is_val e ∨ reducible e.
Proof.
  remember ∅ as Γ. remember 0 as n.
  induction 1 as [| | | | n Γ A B e Hty IH | n Γ A B e Hwf Hwf' Hty IH | n Γ A B e e' x Hwf Hty1 IH1 Hty2 IH2 | | | | n Γ e0 e1 e2 A Hty1 IH1 Hty2 IH2 Hty3 IH3 | n Γ e1 e2 A B Hty IH1 _ IH2 | n Γ e1 e2 op A B C Hop Hty1 IH1 Hty2 IH2 | n Γ e op A B Hop Hty IH | n Γ e1 e2 A B Hty1 IH1 Hty2 IH2 | n Γ e A B Hty IH | n Γ e A B Hty IH | n Γ e A B Hwf Hty IH | n Γ e A B Hwf Hty IH| n Γ e e1 e2 A B C Htye IHe Htye1 IHe1 Htye2 IHe2].
  - subst. naive_solver.
  - left. done.
  - left. done.
  - (* big lambda *) left; done.
  - (* type app *)
    right. destruct (IH HeqΓ Heqn) as [H1|H1].
    + eapply canonical_values_forall in Hty as [e' ->]; last done.
      eexists. eapply base_contextual_step. eapply TBetaS.
    + destruct H1 as [e' H1]. eexists. eauto.
  - (* pack *)
    destruct (IH HeqΓ Heqn) as [H | H].
    + by left.
    + right. destruct H as [e' H]. eexists. eauto.
  - (* unpack *)
    destruct (IH1 HeqΓ Heqn) as [H | H].
    + eapply canonical_values_exists in Hty1 as [e'' ->]; last done.
      right. eexists. eapply base_contextual_step. constructor; last done.
      done.
    + right. destruct H as [e'' H]. eexists. eauto.
  - (* int *)left. done.
  - (* bool*) left. done.
  - (* unit *) left. done.
  - (* if *)
    destruct (IH1 HeqΓ Heqn) as [H1 | H1].
    + eapply canonical_values_bool in Hty1 as (b & ->); last done.
      right. destruct b; eexists; eapply base_contextual_step; constructor.
    + right. destruct H1 as [e0' Hstep].
      eexists. eauto.
  - (* app *)
    destruct (IH2 HeqΓ Heqn) as [H2|H2]; [destruct (IH1 HeqΓ Heqn) as [H1|H1]|].
    + eapply canonical_values_arr in Hty as (x & e & ->); last done.
      right. eexists.
      eapply base_contextual_step, BetaS; eauto.
    + right. destruct H1 as [e1' Hstep].
      eexists. eauto.
    + right. destruct H2 as [e2' H2].
      eexists. eauto.
  - (* binop *)
    assert (A = Int ∧ B = Int) as [-> ->].
    { inversion Hop; subst A B C; done. }
    destruct (IH2 HeqΓ Heqn) as [H2|H2]; [destruct (IH1 HeqΓ Heqn) as [H1|H1]|].
    + right. eapply canonical_values_int in Hty1 as [n1 ->]; last done.
      eapply canonical_values_int in Hty2 as [n2 ->]; last done.
      inversion Hop; subst; simpl.
      all: eexists; eapply base_contextual_step; eapply BinOpS; eauto.
    + right. destruct H1 as [e1' Hstep]. eexists. eauto.
    + right. destruct H2 as [e2' H2]. eexists. eauto.
  - (* unop *)
    inversion Hop; subst A B op.
    + right. destruct (IH HeqΓ Heqn) as [H2 | H2].
      * eapply canonical_values_bool in Hty as [b ->]; last done.
        eexists; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as [e' H2]. eexists. eauto.
    + right. destruct (IH HeqΓ Heqn) as [H2 | H2].
      * eapply canonical_values_int in Hty as [z ->]; last done.
        eexists; eapply base_contextual_step; eapply UnOpS; eauto.
      * destruct H2 as [e' H2]. eexists. eauto.
  - (* pair *)
    destruct (IH2 HeqΓ Heqn) as [H2|H2]; [destruct (IH1 HeqΓ Heqn) as [H1|H1]|].
    + left. done.
    + right. destruct H1 as [e1' Hstep]. eexists. eauto.
    + right. destruct H2 as [e2' H2]. eexists. eauto.
  - (* fst *)
    destruct (IH HeqΓ Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists. eapply base_contextual_step. econstructor; done.
    + right. destruct H as [e' H]. eexists. eauto.
  - (* snd *)
    destruct (IH HeqΓ Heqn) as [H | H].
    + eapply canonical_values_prod in Hty as (e1 & e2 & -> & ? & ?); last done.
      right. eexists. eapply base_contextual_step. econstructor; done.
    + right. destruct H as [e' H]. eexists. eauto.
  - (* injl *)
    destruct (IH HeqΓ Heqn) as [H | H].
    + left. done.
    + right. destruct H as [e' H]. eexists. eauto.
  - (* injr *)
    destruct (IH HeqΓ Heqn) as [H | H].
    + left. done.
    + right. destruct H as [e' H]. eexists. eauto.
  - (* case *)
    right. destruct (IHe HeqΓ Heqn) as [H1|H1].
    + eapply canonical_values_sum in Htye as [(e' & -> & ?) | (e' & -> & ?)]; last done.
      * eexists. eapply base_contextual_step. econstructor. done.
      * eexists. eapply base_contextual_step. econstructor. done.
    + destruct H1 as [e' H1]. eexists. eauto.
Qed.




Definition ectx_typing (K: ectx) (A B: type) :=
  ∀ e, TY 0; ∅ ⊢ e : A → TY 0; ∅ ⊢ (fill K e) : B.


Lemma fill_typing_decompose K e A:
  TY 0; ∅ ⊢ fill K e : A →
  ∃ B, TY 0; ∅ ⊢ e : B ∧ ectx_typing K B A.
Proof.
  unfold ectx_typing; induction K in A |-*; simpl; inversion 1; subst; eauto.
  all: edestruct IHK as (? & ? & ?); eauto.
Qed.

Lemma fill_typing_compose K e A B:
  TY 0; ∅ ⊢ e : B →
  ectx_typing K B A →
  TY 0; ∅ ⊢ fill K e : A.
Proof.
  intros H1 H2; by eapply H2.
Qed.

Lemma fmap_up_subst σ Γ: ⤉(subst σ <$> Γ) = subst (up σ) <$> ⤉Γ.
Proof.
  rewrite -!map_fmap_compose.
  eapply map_fmap_ext. intros x A _. by asimpl.
Qed.

Lemma typed_subst_type n m Γ e A σ:
  TY n; Γ ⊢ e : A → (∀ k, k < n → type_wf m (σ k)) → TY m; (subst σ) <$> Γ ⊢ e : A.[σ].
Proof.
  induction 1 as [ n Γ x A Heq | | | n Γ e A Hty IH | |n Γ A B e Hwf Hwf' Hty IH | n Γ A B e e' x Hwf Hty1 IH1 Hty2 IH2 | | | | | |? ? ? ? ? ? ? ? Hop | ? ? ? ? ? ? Hop | | | | | | ] in σ, m |-*; simpl; intros Hlt; eauto.
  - econstructor. rewrite lookup_fmap Heq //=.
  - econstructor; last by eapply type_wf_subst.
    rewrite -fmap_insert. eauto.
  - econstructor; last by eapply type_wf_subst. eauto.
  - econstructor. rewrite fmap_up_subst. eapply IH.
    intros [| x] Hlt'; rewrite /up //=.
    + econstructor. lia.
    + eapply type_wf_rename; last by (intros ???; simpl; lia).
      eapply Hlt. lia.
  - replace (A.[B/].[σ]) with (A.[up σ].[B.[σ]/]) by by asimpl.
    eauto using type_wf_subst.
  - (* pack *)
    eapply (typed_pack _ _ _ (subst σ B)).
    + eapply type_wf_subst; done.
    + eapply type_wf_subst; first done.
      intros [ | k] Hk; first ( asimpl;constructor; lia).
      rewrite /up //=. eapply type_wf_rename; last by (intros ???; simpl; lia).
      eapply Hlt. lia.
    + replace (A.[up σ].[B.[σ]/]) with (A.[B/].[σ])  by by asimpl.
      eauto using type_wf_subst.
  - (* unpack *)
    eapply (typed_unpack _ _ A.[up σ]).
    + eapply type_wf_subst; done.
    + replace (∃: A.[up σ])%ty with ((∃: A).[σ])%ty by by asimpl.
      eapply IH1. done.
    + rewrite fmap_up_subst. rewrite -fmap_insert.
      replace (B.[σ].[ren (+1)]) with (B.[ren(+1)].[up σ]) by by asimpl.
      eapply IH2.
      intros [ | k] Hk; asimpl; first (constructor; lia).
      eapply type_wf_subst; first (eapply Hlt; lia).
      intros k' Hk'. asimpl. constructor. lia.
  - (* binop *)
    inversion Hop; subst.
    all: econstructor; naive_solver.
  - (* unop *)
    inversion Hop; subst.
    all: econstructor; naive_solver.
  - econstructor; last naive_solver. by eapply type_wf_subst.
  - econstructor; last naive_solver. by eapply type_wf_subst.
Qed.

Lemma typed_subst_type_closed C e A:
  type_wf 0 C → TY 1; ⤉∅ ⊢ e : A → TY 0; ∅ ⊢ e : A.[C/].
Proof.
  intros Hwf Hty. eapply typed_subst_type with (σ := C .: ids) (m := 0) in Hty; last first.
  { intros [|k] Hlt; last lia. done. }
  revert Hty. by rewrite !fmap_empty.
Qed.

Lemma typed_subst_type_closed' x C B e A:
  type_wf 0 A →
  type_wf 1 C →
  type_wf 0 B →
  TY 1; <[x := C]> ∅ ⊢ e : A →
  TY 0; <[x := C.[B/]]> ∅ ⊢ e : A.
Proof.
  intros ??? Hty.
  set (s := (subst (B.:ids))).
  rewrite -(fmap_empty s) -(fmap_insert s).
  replace A with (A.[B/]).
  2: { replace A with (A.[ids]) at 2 by by asimpl.
      eapply type_wf_subst_dom; first done. lia.
  }
  eapply typed_subst_type; first done.
  intros [ | k] Hk; last lia. done.
Qed.

Lemma typed_preservation_base_step e e' A:
  TY 0; ∅ ⊢ e : A →
  base_step e e' →
  TY 0; ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [ | | | op e v v' Heq Heval | op e1 v1 e2 v2 v3 Heq1 Heq2 Heval | | | | | | ]; subst.
  - eapply app_inversion in Hty as (B & H1 & H2).
    destruct x as [|x].
    { eapply lam_anon_inversion in H1 as (C & D & [= -> ->] & Hwf & Hty). done. }
    eapply lam_inversion in H1 as (C & D & Heq & Hwf & Hty).
    injection Heq as -> ->.
    eapply typed_substitutivity; eauto.
  - eapply type_app_inversion in Hty as (B & C & -> & Hwf & Hty).
    eapply type_lam_inversion in Hty as (A & Heq & Hty).
    injection Heq as ->. by eapply typed_subst_type_closed.
  - (* unpack *)
    eapply type_unpack_inversion in Hty as (B & x' & -> & Hwf & Hty1 & Hty2).
    eapply type_pack_inversion in Hty1 as (B' & C & [= <-] & Hty1 & ? & ?).
    eapply typed_substitutivity.
    { apply Hty1. }
    rewrite fmap_empty in Hty2.
    eapply typed_subst_type_closed'; eauto.
    replace A with A.[ids] by by asimpl.
    enough (A.[ids] = A.[ren (+1)]) as -> by done.
    eapply type_wf_subst_dom; first done. intros; lia.
  - (* unop *)
    eapply unop_inversion in Hty as (A1 & Hop & Hty).
    assert ((A1 = Int ∧ A = Int) ∨ (A1 = Bool ∧ A = Bool)) as [(-> & ->) | (-> & ->)].
    { inversion Hop; subst; eauto. }
    + eapply canonical_values_int in Hty as [n ->]; last by eapply is_val_spec; eauto.
      simpl in Heq. injection Heq as <-.
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
    + eapply canonical_values_bool in Hty as [b ->]; last by eapply is_val_spec; eauto.
      simpl in Heq. injection Heq as <-.
      inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
  - (* binop *)
    eapply binop_inversion in Hty as (A1 & A2 & Hop & Hty1 & Hty2).
    assert (A1 = Int ∧ A2 = Int ∧ (A = Int ∨ A = Bool)) as (-> & -> & HC).
    { inversion Hop; subst; eauto. }
    eapply canonical_values_int in Hty1 as [n ->]; last by eapply is_val_spec; eauto.
    eapply canonical_values_int in Hty2 as [m ->]; last by eapply is_val_spec; eauto.
    simpl in Heq1, Heq2. injection Heq1 as <-. injection Heq2 as <-.
    simpl in Heval.
    inversion Hop; subst; simpl in *; injection Heval as <-; constructor.
  - by eapply if_inversion in Hty as (H1 & H2 & H3).
  - by eapply if_inversion in Hty as (H1 & H2 & H3).
  - by eapply fst_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - by eapply snd_inversion in Hty as (B & (? & ? & [= <- <-] & ? & ?)%pair_inversion).
  - eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injl_inversion & ? & ?).
    eauto.
  - eapply case_inversion in Hty as (B & C & (? & ? & [= <- <-] & Hty & ?)%injr_inversion & ? & ?).
    eauto.
Qed.

Lemma typed_preservation e e' A:
  TY 0; ∅ ⊢ e : A →
  contextual_step e e' →
  TY 0; ∅ ⊢ e' : A.
Proof.
  intros Hty Hstep. destruct Hstep as [K e1 e2 -> -> Hstep].
  eapply fill_typing_decompose in Hty as [B [H1 H2]].
  eapply fill_typing_compose; last done.
  by eapply typed_preservation_base_step.
Qed.

Lemma typed_safety e1 e2 A:
  TY 0; ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed.

(** derived typing rules *)
Lemma typed_tapp' n Γ A B C e :
  TY n; Γ ⊢ e : (∀: A) →
  type_wf n B →
  C = A.[B/] →
  TY n; Γ ⊢ e <> : C.
Proof.
 intros; subst C; by eapply typed_tapp.
Qed.
