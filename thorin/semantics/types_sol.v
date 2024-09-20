From stdpp Require Import base relations.
From iris Require Import prelude.
(* From thorin.lib Require Import maps. *)
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


  The most important difference to CC is that we have no rule that types can be beta equivalent
  for typing.
  Additionally, we have normalization operations that are applied eagerly at every construction
*)



Definition typing_context := gmap string expr.
Implicit Types
  (Γ : typing_context)
  (e : expr).


(* TODO: check with page 46 in https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf *)

Require Import Coq.Program.Wf.


Definition Star := Sort 0.
Definition insert_name (x: binder) (e: expr) (Γ: typing_context) :=
  match x with
  | BNamed x => <[x := e]> Γ
  | BAnon => Γ
  end.

(*
We left out zip calculus
and axioms
Without the zip calculus, type assignability becomes normal typing

instead of named and unnamed variants, we use insert_name to unify both into one
*)

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
      (* A has to be typed
      However, we check types at binder position, 
      otherwise type checking ends in an endless loop *)
      TY Γ ⊢ (Var x) : A
    | typed_pi Γ T sT x U sU:
      TY Γ ⊢ T : Sort sT →
      TY (insert_name x T Γ) ⊢ U : Sort sU →
      TY Γ ⊢ (Pi x T U) : (max sT sU)
    | typed_lam Γ x T ef U e sT sU:
      (*
      One might expect TY Γ ⊢ (Pi x T U) : s
      However, we unfold the type to 
      make induction structurally
      *)
      TY Γ ⊢ T : Sort sT →
      TY (insert_name x T Γ) ⊢ U : Sort sU →

      TY (insert_name x T Γ) ⊢ ef : Bool →
      TY (insert_name x T Γ) ⊢ e : U →
      TY Γ ⊢ (Lam x T ef U e) : (Pi x T U)
    | typed_app Γ e eT x T U U':
      TY Γ ⊢ e : (Pi x T U) →
      TY Γ ⊢ eT : T →
      normal_eval (subst' x eT U) U' →
      TY Γ ⊢ (App e eT) : U'
where "'TY' Γ ⊢ e : A" := (syn_typed Γ e%E A%E)
.
#[export] Hint Constructors syn_typed : core.

Lemma typed_weakening Γ Δ e A:
  TY Γ ⊢ e : A →
  Γ ⊆ Δ →
  TY Δ ⊢ e : A.
Proof.
  intros HTy Hsub.
  induction HTy;eauto.
Admitted.






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
Lemma typed_substitutivity e e' Γ (a: binder) A B 
  Γ' e'_norm B'_norm:
  (* TY ∅ ⊢ e' : A → *)
  TY Γ ⊢ e' : A →
  TY (insert_name a A Γ) ⊢ e : B →
  normal_eval (lang.subst' a e' e) e'_norm →
  normal_eval (lang.subst' a e' B) B'_norm →
  (forall x v,
    Γ !! x = Some v <-> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k)) ->
    (* /\ Γ' !! x = Some v -> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k) -> *)
  TY Γ' ⊢ e'_norm : B'_norm.
Proof.
  assert (lang.subst' a e' A = A) as HsubstA by admit.
  intros He' H Hnorme HnormB HΓ.
  (* 
  induction e + inversion lemmas alone are not enough due to dependencies
  subst B : ... is missing => needs hypothesis 
  *)
  revert Γ' e'_norm B'_norm Hnorme HnormB HΓ.
  dependent induction H;simpl;eauto.
  all: intros Γ' e'_norm B'_norm Hnorme HnormB HΓ.
  - (* Sort *)
    replace e'_norm with (Sort n) by admit.
    replace B'_norm with (Sort (S n)) by admit.
    econstructor.
  - (* Bot *)
    replace e'_norm with Bot by admit.
    replace B'_norm with Star by admit.
    econstructor.
  - (* Nat *)
    replace e'_norm with Nat by admit.
    replace B'_norm with Star by admit.
    econstructor.
  - (* Idx *)
    replace e'_norm with Idx by admit.
    replace B'_norm with (Pi BAnon Nat Star) by admit.
    econstructor.
  - (* LitNat *)
    replace e'_norm with (#n)%E by admit.
    replace B'_norm with Nat by admit.
    econstructor.
  - (* LitIdx *)
    replace e'_norm with (LitIdx n i) by admit.
    replace B'_norm with (App Idx n) by admit.
    econstructor.
  - (* Var *)
    replace e'_norm with (Var x) by admit.
    (* needs Environment normalized *)
    econstructor.
    admit. (* relate Γ and Γ' *)
  - (* Pi *)
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in Hnorme by admit.
    (* destruct decide in Hnorme;[admit|]. *)
    assert(
      exists T' U',
      e'_norm = Pi x T' U' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [He'_norm [HnormT HnormU]]]] by admit.
    subst.
    simpl in HnormB.
    replace (B'_norm) with (LitNat(max sT sU)) by admit.
    econstructor.
    + eapply IHsyn_typed1.
      4: eapply HnormT.
      4: admit. (* Sort norm *)
      2: eassumption.
      1: eassumption.
      reflexivity.
      eassumption.
    + eapply IHsyn_typed2.
      4: eassumption.
      4: admit. (* Sort norm *)
      1-2: eassumption.
      admit. (* different order insert *)
      (* eassumption. *)
      admit. (* Γ' *)
  - (* Lambda *)
    replace (subst' a e' (Lam x T ef U e)) with (Lam x (subst' a e' T) (subst' a e' ef) (subst' a e' U) (subst' a e' e)) in Hnorme by admit.
    pose proof HnormB as HnormB2.
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in HnormB2 by admit.
    assert(
      exists T' U' ef' e'',
      e'_norm = Lam x T' ef' U' e'' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' ef) ef' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [ef' [e'' [He'_norm [HnormT [Hnormef HnormU]]]]]]] by admit.
    subst.
    assert(
      exists T'' U'',
      B'_norm = Pi x T'' U'' /\
      normal_eval (subst' a e' T) T'' /\
      normal_eval (subst' a e' U) U''
    ) as [T'' [U'' [HB'_norm [HnormT' HnormU']]]] by admit.
    subst.
    (* confluence of normalize *)
    assert (T' = T'') as -> by admit.
    assert (U' = U'') as -> by admit. 
    econstructor.
    + eapply IHsyn_typed1.
      2-6: try eassumption.
      1-2: eauto.
      all: admit. (* TODO: subst in sort *)
      (* 4: eapply HnormB.
      3: reflexivity.
      1-2: eassumption.
      admit. (* TODO: where does s come from *)
      eassumption. *)
    + eapply IHsyn_typed2.
      4: eassumption.
      1-2: eassumption.
      1: admit. (* insert order *)
      admit. (* bool norm bool *)
      admit. (* Γ' *)
    + admit. (* TODO: assignability induction *)
    + admit. (* TODO: *)
  - (* App *)
    admit. (* TODO *)
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
Admitted.


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
Admitted.










(*
Progress 
|- e : A
=================
e is a value or
exists e' s.t. e -> e'
*)
(*
  TODO: need empty env => variable is not a value and not reducible
*)
(*
but this does not work for U in Pi, for instance, we need a different env
=> reduction under binder
Corollary typed_progress e A:
  TY ∅ ⊢ e : A →
  is_val e ∨ reducible e.
Proof.
  intros HTy.
  remember ∅ as Γ eqn:HΓ.
  induction HTy.
  all: subst;eauto 10 using is_val.
  - admit. (* in empty env, we would not have var *)
  - (* Pi *)
*)


Corollary typed_progress Γ e A:
  TY Γ ⊢ e : A →
  is_val e ∨ reducible e.
Proof.
  intros HTy.
  induction HTy.
  all: subst;eauto 10 using is_val.
  - admit. (* in empty env, we would not have var *)
  (* 
  - (* Pi *)
    destruct IHHTy1 as [HvalT|[? ?]].
    + destruct IHHTy2 as [HvalU|[? ?]].
      (* * destruct IHHTy4 as [Hvale|[? ?]];[|right;eexists;eauto].
        left. 
        now constructor. *)
      * right. eexists. eauto.
    + right. eexists. eauto.
    *)
  - (* Lambda *)
    destruct IHHTy4 as [Hvale|[? ?]];[|right;eexists;eauto].
    destruct IHHTy2 as [HvalU|[? ?]];[|right;eexists;eauto].
    destruct IHHTy1 as [HvalT|[? ?]];[|right;eexists;eauto].
    left. 
    now constructor.
  - (* App *)
    (* only value for Idx n *)
    destruct IHHTy1 as [Hvale|[? ?]];[|right;eexists;eauto].
    destruct IHHTy2 as [Hvale2|[? ?]];[|right;eexists;eauto].
    specialize (canonical_value_pi _ _ _ _ _ HTy1 Hvale) as [(->&->&->&->)|(f&ef&->)].
    + (* Idx *)
      specialize (canonical_value_nat _ _ HTy2 Hvale2) as [m ->].
      left. constructor.
    + right. eexists. eapply base_contextual_step.
      eapply BetaS. reflexivity.
Admitted.


Lemma Forall2_nth_error {X Y:Type} (P: X -> Y -> Prop) xs ys:
  Forall2 P xs ys →
  forall i x,
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



(*
General Preservation Idea:

If typed expression steps, it is typed.
But expressions can change their type, hence the type has to step too.

After a step, we need normalized expressions. Hence, we normalize both before type checking.

Furthermore, the change of typed in argument position breaks type dependencies.
Hence, one beta step is not enough.
Therefore, only eventually (after multiple step), a consistent (typed) state is reached.


Γ ⊢ e : A
e →β e'
=================
∃ e'' e''' A' A''
e' →*β e'' →n e'''
A  →*β A'  →n A''
Γ ⊢ e''' : A''

*)

(*
stronger than (probably necessary) but provable

Note base_step is only toplevel (→ᵦ is also contextual)
*)
Lemma typed_preservation_base_step e e' Γ A
  e'_norm:
  TY Γ ⊢ e : A →
  base_step e e' →
  normal_eval e' e'_norm →
  TY Γ ⊢ e'_norm : A.
Proof.
  intros Hty Hstep Hnorm.
  inversion Hstep;subst.
  inversion Hty;subst;eauto using is_val.
  inversion H1;subst.

  eapply typed_substitutivity.
  3-4: eassumption.
  2: eassumption.
  1: eassumption.
  admit. (* simple *)
Admitted.

Lemma fill_step K e1 e2:
  base_step e1 e2 ->
  fill K e1 →ᵦ fill K e2.
Proof.
  econstructor;eauto.
Qed.

















(*
just symmetry, refl, trans +
(lam A. B) C = B [x := C]

or via beta
*)
Definition equiv (A B:expr) := True.
Notation "A ≡ᵦ B" := (equiv A B) (at level 70).


Reserved Notation "'TY' Γ ⊢ᵦ e : A" (at level 74, e, A at next level).
Reserved Notation "'TY' Γ ⊢ᵦ A ← e" (at level 74, e, A at next level).
Inductive beta_syn_typed : typing_context → expr → expr → Prop :=
   | beta_typed_sort Γ n:
      TY Γ ⊢ᵦ Sort n : Sort (S n)
   | beta_typed_bot Γ:
      TY Γ ⊢ᵦ Bot : Star
   | beta_typed_nat Γ:
      TY Γ ⊢ᵦ Nat : Star
   | beta_typed_idx Γ:
      TY Γ ⊢ᵦ Idx : (Pi BAnon Nat Star)
   | beta_typed_lit_nat Γ n:
      TY Γ ⊢ᵦ (#n)%E : Nat
    | beta_typed_lit_idx Γ n i:
      TY Γ ⊢ᵦ (LitIdx n i) : (App Idx n)
    | beta_typed_var Γ x A :
      Γ !! x = Some A →
      TY Γ ⊢ᵦ (Var x) : A
    | beta_typed_pi Γ T sT x U sU:
      TY Γ ⊢ᵦ T : Sort sT →
      TY (insert_name x T Γ) ⊢ᵦ U : Sort sU →
      TY Γ ⊢ᵦ (Pi x T U) : (max sT sU)
    | beta_typed_lam Γ x T ef U e sT sU:
      TY Γ ⊢ᵦ T : Sort sT →
      TY (insert_name x T Γ) ⊢ᵦ U : Sort sU →

      TY (insert_name x T Γ) ⊢ᵦ ef : Bool →
      TY (insert_name x T Γ) ⊢ᵦ e : U →
      TY Γ ⊢ᵦ (Lam x T ef U e) : (Pi x T U)
    | beta_typed_app Γ e eT x T U U':
      TY Γ ⊢ᵦ e : (Pi x T U) →
      TY Γ ⊢ᵦ eT : T →
      normal_eval (subst' x eT U) U' →
      TY Γ ⊢ᵦ (App e eT) : U'
    | beta_typed_conv Γ e A B:
      TY Γ ⊢ᵦ e : A →
      A ≡ᵦ B →
      TY Γ ⊢ᵦ e : B
where "'TY' Γ ⊢ᵦ e : A" := (beta_syn_typed Γ e%E A%E)
.
#[export] Hint Constructors beta_syn_typed : core.



Lemma subst_sort x e n:
  subst' x e (Sort n) = Sort n.
Proof.
  destruct x; reflexivity.
Qed.

Lemma normalize_sort n e:
  Sort n →ₙ e -> 
  e = Sort n.
Proof.
  intros H.
  inversion H;subst.
  inversion H0;subst.
  1: reflexivity.
  inversion H2;subst.
  destruct K;simpl in *;inversion H4;subst.
  inversion H6.
Qed.

Lemma normalized_app e1 e2:
  normalized_pred (e1 e2) ->
  normalized_pred e1 ∧ normalized_pred e2.
Proof.
  intros H.
  (* unfold normalized_pred in H. *)
  split.
  - unfold normalized_pred in *.
    contradict H.
    destruct H as [e1' [K ei1 ei2 He1]].
    exists (e1' e2).
    econstructor.
    instantiate (2:= FApp1 K e2).
    all: simpl;f_equal;eauto.
  - (* analogous *)
    unfold normalized_pred in *.
    contradict H.
    destruct H as [e2' [K ei1 ei2 He2]].
    exists (e1 e2').
    econstructor.
    instantiate (2:= FApp2 e1 K).
    all: simpl;f_equal;eauto.
Qed.


Lemma app_norm e1 e2 en:
  e1 e2 →ₙ en ->
  (
    exists e1' e2', 
    e1 →ₙ e1' /\ e2 →ₙ e2' /\ 
    (
      en = e1' e2' \/
      (exists e',
        normalize_step (e1' e2') e' /\
        e' →ₙ en
      )
    )
  ).
Proof.
  intros H.
  inversion H;subst.
  dependent induction H0.
  (* look at full_contextual_steps and whether one is toplevel
    if -> found point 
    else: recursion
  *)
  - exists e1, e2.
    apply normalized_app in H1 as [Hn1 Hn2].
    split;[|split].
    3: eauto.
    all: constructor;eauto;constructor.
  - destruct H1.
    assert (K = FHoleCtx \/ exists K', K = FApp1 K' e2 \/ K = FApp2 e1 K') as [->|[K' [-> | ->]]].
    {
      subst.
      destruct K;simpl in *;inversion H1;subst;eauto.
    }
    + simpl in *;subst.
      (* TODO:
      these are e1 ->n e1' and e2 ->n e2'
      do these need to be full to end normalizations? (probably?)
      => TODO: need to restrict full_contextual_steps to have normalized subexpression
       *)
      exists e1, e2.
      assert(
        normalized_pred e1 ∧ normalized_pred e2
      ) as [Hn1 Hn2].
      {
        inversion H4;subst.
      }
      split;[|split].
      3: {
       right.
       exists e2'.
       split;eauto.
       constructor;eassumption.
      }
      all: constructor;eauto;constructor.
    + (* not toplevel => just continue *)
      simpl in *;subst.
      inversion H1;subst.
      specialize (IHrtc (full_fill K' e2') e2).
      edestruct IHrtc as [f1 [f2 [Hf1 [Hf2 [-> | [f' [Hstep Hnorm]]]]]]];eauto.
      1: constructor;eauto.
      * exists f1, f2. 
        split;[|split].
        2-3: eauto.
        destruct Hf1.
        constructor;eauto.
        econstructor.
        2: eassumption.
        econstructor;eauto.
      * exists f1, f2.
        split;[|split].
        2: assumption.
        1: {
          destruct Hf1.
          constructor;eauto.
          econstructor.
          2: eauto.
          econstructor;eauto.
        }
        right.
        exists f'. 
        split;eauto.
Admitted.






Lemma beta_typed_substitutivity e e' Γ (a: binder) A B 
  Γ' e'_norm B'_norm:
  TY Γ ⊢ᵦ e' : A →
  TY (insert_name a A Γ) ⊢ᵦ e : B →
  normal_eval (lang.subst' a e' e) e'_norm →
  normal_eval (lang.subst' a e' B) B'_norm →
  (forall x v,
    Γ !! x = Some v <-> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k)) ->
    (* /\ Γ' !! x = Some v -> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k) -> *)
  TY Γ' ⊢ᵦ e'_norm : B'_norm.
Proof.
  assert (lang.subst' a e' A = A) as HsubstA by admit.
  intros He' H Hnorme HnormB HΓ.
  (* 
  induction e + inversion lemmas alone are not enough due to dependencies
  subst B : ... is missing => needs hypothesis 
  *)
  revert Γ' e'_norm B'_norm Hnorme HnormB HΓ.
  dependent induction H;simpl;eauto.
  all: intros Γ' e'_norm B'_norm Hnorme HnormB HΓ.
  - (* Sort *)
    rewrite subst_sort in Hnorme.
    rewrite subst_sort in HnormB.
    apply normalize_sort in Hnorme as ->.
    apply normalize_sort in HnormB as ->.
    econstructor.
  - (* Bot *)
    replace e'_norm with Bot by admit.
    replace B'_norm with Star by admit.
    econstructor.
  - (* Nat *)
    replace e'_norm with Nat by admit.
    replace B'_norm with Star by admit.
    econstructor.
  - (* Idx *)
    replace e'_norm with Idx by admit.
    replace B'_norm with (Pi BAnon Nat Star) by admit.
    econstructor.
  - (* LitNat *)
    replace e'_norm with (#n)%E by admit.
    replace B'_norm with Nat by admit.
    econstructor.
  - (* LitIdx *)
    replace e'_norm with (LitIdx n i) by admit.
    replace B'_norm with (App Idx n) by admit.
    econstructor.
  - (* Var *)
    replace e'_norm with (Var x) by admit.
    (* needs Environment normalized *)
    econstructor.
    admit. (* relate Γ and Γ' *)
  - (* Pi *)
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in Hnorme by admit.
    (* destruct decide in Hnorme;[admit|]. *)
    assert(
      exists T' U',
      e'_norm = Pi x T' U' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [He'_norm [HnormT HnormU]]]] by admit.
    subst.
    simpl in HnormB.
    replace (B'_norm) with (LitNat(max sT sU)) by admit.
    econstructor.
    + eapply IHbeta_syn_typed1.
      4: eapply HnormT.
      4: admit. (* Sort norm *)
      2: eassumption.
      1: eassumption.
      reflexivity.
      eassumption.
    + eapply IHbeta_syn_typed2.
      4: eassumption.
      4: admit. (* Sort norm *)
      1-2: eassumption.
      admit. (* different order insert *)
      (* eassumption. *)
      admit. (* Γ' *)
  - (* Lambda *)
    replace (subst' a e' (Lam x T ef U e)) with (Lam x (subst' a e' T) (subst' a e' ef) (subst' a e' U) (subst' a e' e)) in Hnorme by admit.
    pose proof HnormB as HnormB2.
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in HnormB2 by admit.
    assert(
      exists T' U' ef' e'',
      e'_norm = Lam x T' ef' U' e'' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' ef) ef' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [ef' [e'' [He'_norm [HnormT [Hnormef HnormU]]]]]]] by admit.
    subst.
    assert(
      exists T'' U'',
      B'_norm = Pi x T'' U'' /\
      normal_eval (subst' a e' T) T'' /\
      normal_eval (subst' a e' U) U''
    ) as [T'' [U'' [HB'_norm [HnormT' HnormU']]]] by admit.
    subst.
    (* confluence of normalize *)
    assert (T' = T'') as -> by admit.
    assert (U' = U'') as -> by admit. 
    econstructor.
    + eapply IHbeta_syn_typed1.
      2-6: try eassumption.
      1-2: eauto.
      all: admit. (* TODO: subst in sort *)
      (* 4: eapply HnormB.
      3: reflexivity.
      1-2: eassumption.
      admit. (* TODO: where does s come from *)
      eassumption. *)
    + eapply IHbeta_syn_typed2.
      4: eassumption.
      1-2: eassumption.
      1: admit. (* insert order *)
      admit. (* bool norm bool *)
      admit. (* Γ' *)
    + admit. (* TODO: assignability induction *)
    + admit. (* TODO: *)
  - (* App *)
    (* norm can beta or just norm in subterms *)
    replace(subst' a e' (e eT)) with ((subst' a e' e) (subst' a e' eT)) in Hnorme.
    2: {
      destruct a; simpl;reflexivity.
    }
    assert(
      exists se' seT',
      subst' a e' e →ₙ se' /\
      subst' a e' eT →ₙ seT' /\
      e'_norm = App se' seT'
    ) as [se' [seT' [Hse' [HseT' ->]]]] by admit.
    eapply beta_typed_app.
    + eapply IHbeta_syn_typed1;eauto. admit. (* type norm *)
    + eapply IHbeta_syn_typed2;eauto. admit. (* type norm *)
Admitted.






Lemma beta_preservation Γ e e' A:
  TY Γ ⊢ᵦ e : A ->
  e →ᵦₙ e' ->
  TY Γ ⊢ᵦ e' : A.
Proof.
  intros HTy Hstep.
  destruct Hstep as [e'' [Hbeta Hnorm]].
  destruct Hbeta as [K e1 e2 -> -> Hstep].
  revert e2 Hstep e' Hnorm.
  dependent induction HTy;intros e2 Hstep e' Hnorm;cbn in *.
  all: try now (destruct K;cbn in *;inversion x;subst;inversion Hstep).
  (* 
  - admit. (* Sort *)
  - admit. (* Bot *)
  - (* Nat *)
    destruct K;cbn in *;inversion x;subst;inversion Hstep.
  - admit. (* Idx *)
  - admit. (* LitNat *)
  - admit. (* LitIdx *)
  - admit. (* Var *)
  *)

  - (* Pi *)
    destruct K;cbn in *;inversion x;subst.
    + inversion Hstep.
    + (* step in Type *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Pi x1 Ke2' U0
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_pi.
      * eapply IHHTy1;eauto.
      * (* step in context *)
        admit.
    + (* step in codom *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Pi x1 T0 Ke2'
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_pi.
      * eassumption.
      * eapply IHHTy2;eauto.
  - (* Lam *)
    destruct K;cbn in *;inversion x;subst.
    + inversion Hstep.
    + (* step in Type *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x1 Ke2' f U0 e0
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_conv.
      eapply beta_typed_lam;eauto.
      1-3: admit. (* step in context *)
      admit. (* beta conversion *)
    + (* step in codom *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x1 T0 f Ke2' e0
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_conv.
      eapply beta_typed_lam;eauto.
      * eapply beta_typed_conv.
        1: eassumption.
        admit. (* beta conversion *)
      * admit. (* beta conversion *)
    + (* body *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x1 T0 f U0 Ke2'
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_lam;eauto.
  - (* App *)
    destruct K;cbn in *;inversion x;subst.
    (* case left *)
    2: {
      (* maybe normalize evaluates redex *)
      assert(exists Ke2',
        fill K e2 →ₙ Ke2'
      ) as [Ke2' HKe2norm] by admit.
      assert (TY Γ ⊢ᵦ Ke2' v2 : U') as Hty.
      {
        eapply beta_typed_app.
        - eapply IHHTy1;eauto.
        - eauto.
        - eauto.
      }
      (* if normalization of toplevel redex => done *)

      (* just case distinction on normalization? *)
      (*
        e1 e2 ->n en
        e1 ->n e1n
        e2 ->n e2n

        en = e1n e2n \/ e1n e2n toplevel normalize to en' and en' ->n en
      *)


      (* assert (base_step (App Ke2' v2) e') as Hstep' by admit. *)
      assert (normalize_step (App Ke2' v2) e') as Hstep' by admit.
      inversion Hstep';subst.
      rename eb into elam.

      (* inversion Hstep';subst. *)
      pose proof typed_substitutivity.
      specialize (H0 elam v2 Γ x1).
      specialize (H0 T).
      replace (syn_typed) with beta_syn_typed in H0 by admit.
      assert(TY (insert_name x1 T Γ) ⊢ᵦ elam : U0) as Htyelam by admit.
      (* assert (x=x0) as ->.  {
        inversion HTy1;eauto.
        admit.
      } *)
      specialize (H0 U0 Γ).

      inversion Hty;subst.
      2: {
        admit. (* TODO: subst in elam is typed *)
      }
      inversion H3;subst.
      2: {
        admit. (* TODO: beta case *)
      }
      eapply H0;eauto.
      1: admit. (* TODO: normalize on normalized values *)
      admit. (* env subst *)
    }
    (* case right *)
    2: {
      assert(exists Ke2',
        fill K e2 →ₙ Ke2'
      ) as [Ke2' HKe2norm] by admit.
      assert (exists Ue2', subst' x0 Ke2' U →ₙ Ue2') as [Ue2' HUe2norm] by admit.
      assert (TY Γ ⊢ᵦ e0 Ke2' : U') as Hty.
      {
        eapply beta_typed_conv with (A:=Ue2').
        eapply beta_typed_app.
        - eauto.
        - eapply IHHTy2;eauto.
        - assumption.
        - admit. (* beta under subst *)
      }
      admit. (* toplevel case *)
    }
    (* admit. *)
    (* case toplevel *)
    (* assert (K=HoleCtx) as -> by admit. *)
    (* simpl in *.
    subst. *)
    inversion Hstep;subst.
    Check typed_substitutivity.
    pose proof typed_substitutivity.
    specialize (H1 elam eT Γ x).
    specialize (H1 T).
    replace (syn_typed) with beta_syn_typed in H1 by admit.
    (* assert(exists B',
      TY (insert_name x T Γ) ⊢ᵦ elam : B'
    ) as [B' Htyelam] by admit. *)
    assert(TY (insert_name x T Γ) ⊢ᵦ elam : U) as Htyelam by admit.
    assert (x=x0) as ->.  {
      inversion HTy1;subst;eauto.
      admit. (* type conversion case *)
    }
    specialize (H1 U Γ e').
    eapply H1;eauto.
    admit. (* subst in env *)
    (* inversion HTy1;subst. *) 
    (* we have problem to know norm result *)
  - (* equiv *)
    eapply beta_typed_conv.
    1: {
      eapply IHHTy.
      all: try eassumption.
      reflexivity.
    }
    assumption.
Admitted.


















































































Definition equivalent e1 e2 :=
  exists e', e1 →ᵦₙ* e' ∧ e2 →ᵦₙ* e'.

Notation "e1 ≡ e2" := (equivalent e1 e2) (at level 70).

(*
if two expressions are typed and equivalent
then their types are equivalent
*)
Lemma equivalent_types e1 e2 A1 A2 Γ:
  TY Γ ⊢ e1 : A1 →
  TY Γ ⊢ e2 : A2 →
  e1 ≡ e2 →
  A1 ≡ A2.
Proof.
  intros HTy1 HTy2 Heq.
  destruct Heq as [e' [H1 H2]].
  induction H1 in e2,H2,HTy1,HTy2 |-*.
  - admit. (* base step *)
  - admit. (* transitivity *)

  (*
  
  could go e1 last step to e'
  now back what is intermediate

  e' does not necessarily need to be typed
  *)






(* 
like beta but annotated with evaluation point 
for partial application, we want ep as first argument
however, from the type point, ep is a non-uniform parameter
*)
Inductive graded_contextual_step (ep:expr) (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    ep = e1' →
    base_step e1' e2' → graded_contextual_step ep e1 e2.

Notation "e →[ ep ]ᵦ e'" := (graded_contextual_step ep e e') (at level 50).
Notation "e →[ ep ]ᵦ* e'" := (rtc (graded_contextual_step ep) e e') (at level 50).

Definition beta_normal_step ep e e' :=
  exists e_aux, e →[ep]ᵦ e_aux /\ e_aux →ₙ e'.

Notation "e →[ ep ]ᵦₙ e'" := (beta_normal_step ep e e') (at level 50).
Notation "e →[ ep ]ᵦₙ* e'" := (rtc (beta_normal_step ep) e e') (at level 50).



(*
Idea: dependencies can only be between lambda and its argument
=> if doing a step with ep, we need to do more of them to reach a stable state

Similarly, our type change is caused by a reduction, hence the change is the same as this reduction
*)

Definition all_beta_steps b e e' :=
  e →[b]ᵦₙ* e' /\ ~ exists e'', e' →[b]ᵦ e''.

Notation "e →|[ ep ] e'" := (all_beta_steps ep e e') (at level 50).

(*
single or uncoordinated parallel steps are not enough
for typing, we need special steps

=> we need to do all (maybe direct not recursive) "special" steps 

TODO: can be do all steps instead?

*)



Lemma typed_preservation_eventually
  Γ e A:
  TY Γ ⊢ e : A →
  forall e' A' b,
  e →|[b] e' →
  A →|[b] A' →
  TY Γ ⊢ e' : A'.
Proof.
  intros HTy. 
  pose proof (HTyCpy := HTy).
  induction HTy.
  (* do not step *)
  1,2,3,4,5,6,7: admit.
  (* only Pi, Lam, App left *)
  all: intros e' A' b Hstepe HstepA.
  - (* Pi *)
    assert (
      exists T' U',
      e' = Pi x T' U' /\ 
      T →|[b] T' /\
      U →|[b] U'
    ) as (T'&U'&->&HT&HU) by admit.
    assert (A' = LitNat(sT `max` sU)) as -> by admit.
    apply typed_pi.
    + eapply IHHTy1;eauto.
      admit. (* Sort -> Sort *)
    + replace (T') with T by admit. (* step in env *)
      eapply IHHTy2;eauto.
      admit. (* Sort -> Sort *)
  - (* Lam *)
    rename e into eB.
    assert(
      exists T' ef' U' eB',
      T →|[b] T' /\
      U →|[b] U' /\
      ef →|[b] ef' /\
      eB →|[b] eB' /\
      e' = Lam x T' ef' U' eB'
    ) as (
      T'&ef'&U'&eB'&
      HT&HU&Hef&HeB&->
    ) by admit.

    assert (
      exists T'' U'',
      A' = Pi x T'' U'' /\ 
      T →|[b] T'' /\
      U →|[b] U''
    ) as (T''&U''&->&HT2&HU2) by admit.

    replace T'' with T' by admit. (* Deterministic →| *)
    replace U'' with U' by admit. (* Deterministic →| *)
    econstructor.
    1: {
      eapply IHHTy1;eauto.
      admit. (* Sort -> Sort *)
    }
    all: replace T' with T by admit. (* step in env *)
    + eapply IHHTy2;eauto. admit. (* Sort -> Sort *)
    + eapply IHHTy3;eauto. admit. (* Bool -> Bool *)
    + eapply IHHTy4;eauto.


  - (* App *)
    rename e into eL.
    rename U' into sU.
    rename A' into sU'.

    (* simplified case *)
    assert(
      exists eL' eT',
      eL →|[b] eL' /\
      eT →|[b] eT' /\
      e' = eL' eT'
    ) as (eL'&eT'&HeL&HeT&->) by admit.

    assert (
      exists T' U',
      Pi x T U →|[b] Pi x T' U' /\
      T →|[b] T' /\
      U →|[b] U'
    ) as (T'&U'&HPi&HT&HU) by admit.

    econstructor.
    1: {
      eapply IHHTy1;eauto.
    }
    1: {
      eapply IHHTy2;eauto.
    }


    (*
      here is an important difference to general beta
      (or eval to value directly):
      - 

      U[eT/x] ->n sU
      sU ->| sU'
      U ->| U'
      eT ->| eT'



      we want: 
      U'[eT'/x] ->n sU'


      we have (subst lemma)
      U[eT/x] ->* normalized(U'[eT'/x])

      and U[eT/x] ->| sU'

      by triangle lemma
      U'[eT'/x] ->| sU'
      but we need that normalization is enough


      Steps after sub can be done before
      and no relevant step contradicted by subst
      but:
      argument is a lambda => creates redex after subst



      by uniqueness of normalization, this is sU'




      idea:
      sU does all its eval steps in eT' and the one in U
      TODO: why no overlap => why not sub into b? (e.g. why are U subst sites not destroyed)

      b does not change eT 
      or it is closed in the env of eT

      x free in b:
        eT' = eT

      x not free in b:
        subst x does not interfere with eval points (just might add some)
        i.e. subst x expr b = b
        statement holds

      if x free:
        then unify all free vars => anything that is placed in for x can be unified with x => use it
    *)
    admit.
Qed.


(*

does not work => we have b steps but know nothing => same problem

Lemma typed_preservation_eventually
  Γ e A:
  TY Γ ⊢ e : A →
  forall e' A' b,
  e →[b]ᵦₙ* e' →
  A →[b]ᵦₙ* A' →
  exists e'' A'',
  e' →[b]ᵦₙ* e'' ∧
  A' →[b]ᵦₙ* A'' ∧
  TY Γ ⊢ e'' : A''.
Proof.
  intros HTy. 
  induction HTy.
  (* do not step *)
  1,2,3,4,5,6,7: admit.
  (* only Pi, Lam, App left *)
  all: intros e' A' b Hstepe HstepA.
  - (* Pi *)
    admit.
  - (* Lam *)
    admit.
  - (* App *)
    rename e into eA.
    idtac.
    assert  (
      exists eT',
      eT →[ b ]ᵦₙ* eT' /\ 
      e' = eA eT'
    ) as (eT'&HstepeT&->) by admit.
 *)



(* Lemma typed_preservation_eventually
  Γ e A:
  TY Γ ⊢ e : A →
  forall e',
  e →ᵦₙ* e' →
  exists e'' A' A'',
  A →ᵦₙ* A' ∧
  e' →ᵦₙ* e'' ∧
  A' →ᵦₙ* A'' ∧
  TY Γ ⊢ e'' : A''.
Proof.
  intros HTy e' Hstep.
  induction Hstep.
  - do 3 eexists. 
    split;[|split;[|split]].
    1-3: constructor.
    assumption.
  -   
    enough (
      ∃ e'' A' A'' : expr, A →ᵦₙ* A' ∧ y →ᵦₙ* e'' ∧ A' →ᵦₙ* A'' ∧ TY Γ ⊢ e'' : A''
    ).
    {
      destruct H0 as (?&?&?&?&?&?&?).
      do 3 eexists.
      split;[|split;[|split]].
      4: apply H3.
      1,3:eassumption.
      admit. (* would need confluence *)
    } 
Abort. *)


(*
if typed expression takes one step
than it can take a few more to reach a typed state.

newest generalization:
if either expression or type steps both step further to a combined finished state
*)
Lemma typed_preservation_eventually
  Γ e A:
  TY Γ ⊢ e : A →
  forall e' A',
  e →ᵦₙ* e' →
  A →ᵦₙ* A' →
  exists e'' A'',
  e' →ᵦₙ* e'' ∧
  A' →ᵦₙ* A'' ∧
  TY Γ ⊢ e'' : A''.
Proof.
  intros HTy. 
  induction HTy.
  (* do not step *)
  1,2,3,4,5,6,7: admit.
  (* only Pi, Lam, App left *)
  all: intros e' A' Hstepe HstepA.
  - (* Pi *)
    (*
      e' = Pi x T' U'
      s.t.
      T →ᵦₙ* T'
      U →ᵦₙ* U'

      by IH we have 
      typed 
      T'' and U''

      need env step as U might depend on T
    *)
    admit.
  - (* Lam *)
    (*
      Lambda also has no toplevel step but is has dependencies directly 

      each component steps and then steps to adhere to other
      => maybe our IH is good enough, TODO: check

    *)
    admit.
  - (* App *)
    (*
      either subcomponent steps or toplevel
      (or all in different time steps)

      Idea:
      first step is toplevel
      or steps before
      decompose: 
        both sides step then maybe toplevel, then maybe more

      eT steps to eT' (and T might step somewhere)
      by IH we get eT'' and T'' s.t.
      eT'' : T''

      now we know that T steps to T''
      e steps to e 
      and Pi x T U to Pi x T'' U
      then we get 


      mh do we need confluence?
    *)
    rename e into eA.
    idtac.



  (*
    destruct on context
  *)
  
Admitted.








(* Difference to onestep: we have →ᵦ* instead of just one step *)
Lemma typed_preservation_eventually_invers:
  (forall Γ e A (H:TY Γ ⊢ e : A),
  forall (HTy: TY Γ ⊢ e : A), 
    forall A', A →ᵦ* A' →

    (* we need the same eventual-stepping as types can be as weird as expressions *)
    exists e' e'' A'' A''',
    TY Γ ⊢ e'' : A''' ∧
    (e →ᵦ* e' ∧ e' →ₙ e'') ∧
    (A' →ᵦ* A'' ∧ A'' →ₙ A''')
  ).
Proof.
(* maybe we need induction over K? *)
  (* intros ? ? ? H.
  induction H.
  all: intros HTy -> A' Hstep.
  all: destruct Hstep as [K e1 e2 He1 He2 Hstep];subst.
  all: destruct K;simpl in *;try congruence.
  all: subst.
  all: try now inversion Hstep.
  all: try inversion He1;subst.
  - admit.
  - admit.
  - admit.
  - admit. *)
Admitted.


 Corollary typed_preservation_eventually_invers_onestep:
  (forall Γ e A (H:TY Γ ⊢ e : A),
  forall (HTy: TY Γ ⊢ e : A), 
    forall A', A →ᵦ A' →

    (* we need the same eventual-stepping as types can be as weird as expressions *)
    exists e' e'' A'' A''',
    TY Γ ⊢ e'' : A''' ∧
    (e →ᵦ* e' ∧ e' →ₙ e'') ∧
    (A' →ᵦ* A'' ∧ A'' →ₙ A''')
  ).
Proof.
Admitted.



(*
If expression steps, it is eventually typed again
*)
Lemma typed_preservation_eventually:
  (forall Γ e A (H:TY Γ ⊢ e : A),
  forall (HTy: TY Γ ⊢ e : A), 
    (* Γ = ∅ → *)
    forall e', e →ᵦ e' →
    exists e'' e''' A' A'',
    TY Γ ⊢ e''' : A'' ∧
    (e' →ᵦ* e'' ∧ e'' →ₙ e''') ∧
    (A →ᵦ* A' ∧ A' →ₙ A'')
  ).
Proof.
  intros ? ? ? H.
  induction H.
  all: intros HTy e' Hstep.

  all: destruct Hstep as [K e1 e2 He1 He2 Hstep];subst.
  all: destruct K;simpl in *;try congruence.
  all: subst.
  all: try now inversion Hstep.
  all: try inversion He1;subst.
  (* the type of a lam will also come up *)
  (* also return type => if we have e_{2+2} in the body, the return type changes from Idx (2+2) to Idx(4) *)
  - (* Pi domain *)

    (* e1 takes one step to e2
    by IH 
    fill K e1 takes a few steps until typed again

    extend those steps to Pi 
    and but is U still typed under this? (in env x:T)

    if step in context => still typed => see paper again (page 58)
    *)
    specialize (IHsyn_typed1 H (fill K e2)).
    edestruct IHsyn_typed1 as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA'&HN'A)).
    1: now apply fill_step.
    assert (TY (insert_name x0 Ke2'' Γ) ⊢ U0 : Sort sU) by admit. (* Assumption step *)
    (* TODO: U0 already normalized *)
    (* assert (Pi'' = Pi x0 Ke2'' U0) as -> by admit.
    assert (exists Pi'', 
      normal_eval (Pi x0 Ke2' U0) Pi'') as [Pi'' HPi''] by admit. *)
    assert (
      normal_eval (Pi x0 Ke2' U0) (Pi x0 Ke2'' U0)
    ) by admit.
    assert (A'' = Sort sT) as -> by admit. (* inversion Sort beta, norm *)
    exists (Pi x0 Ke2' U0).
    exists (Pi x0 Ke2'' U0).
    do 2 eexists.
    split;[|split;split].
    2-3: admit. (* easy, Pi congruence beta norm *)
    1: apply typed_pi;eassumption.
    1-2: admit. (* easy, LitNat beta norm *)

  - (* Pi codomain *)
    (* specialize (IHsyn_typed2 H0 eq_refl (fill K e2)). *)
    edestruct IHsyn_typed2 as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA'&HN'A)).
    1: assumption.
    1: eapply fill_step;eassumption.
    exists (Pi x0 T0 Ke2').
    exists (Pi x0 T0 Ke2''). (* T0 already normalized *)
    do 2 exists (LitNat (sT `max` sU)).
    split;[|split;split].
    4-5: admit. (* easy LitNat beta norm *)
    2-3: admit. (* easy Pi beta norm congruence *)
    constructor.
    1: eassumption.
    assert(A'' = Sort sU) as -> by admit. (* Sort inversion beta norm *)
    assumption.

  - (* domain Type of lambda *)
  (*
    same as above:
    we follow the beta,
    everything else is normalized and no top-level normalization
    => just follow subexpression
  *)
  (*
    special as our type recursion is on Pi not T and U
    still possible (just do 2 beta step chains) but probably individually easier
  *)
    specialize (IHsyn_typed1 H (fill K e2)).
    edestruct IHsyn_typed1 as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA'&HN'A)).
    1: now apply fill_step.
    assert (A'' = Sort sT) as -> by admit. (* Sort inversion beta norm *)
    exists (Lam x0 Ke2' f U0 e0).
    exists (Lam x0 Ke2'' f U0 e0).
    exists (Pi x0 Ke2' U0).
    exists (Pi x0 Ke2'' U0).
    split;[|split;split].
    1: {
      eapply typed_lam.
      1: eassumption.
      all: admit. (* TODO: step in assumption *)
    }
    1-2: admit. (* easy *)
    1-2: admit. (* easy *)

  - (* codomain of Lambda *)

    (*
      The codomain changes 
      => body needs to step the change 

      currently, we have preservation as:
      if expression steps, there is a stepped type

      here, we need
      if type steps, expression can step too


      confluence/church rosser alone would not be enough
      The statement would be:
        e moves not has a type resulting from the old one
        both meet => 
          we get a new type of body expression (by IH as body steps)
          by confluence this stepped from the original codomain
        (we need that it steps at least one time but we can do this by value distinction and contradiction)
      however, for this we need that the body steps which we do not have
    *)


    (* edestruct IHsyn_typed2 as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA'&HN'A)).
    1: eassumption.
    1: admit. (* extended context *)
    1: eapply fill_step;eassumption.
    assert (A'' = Sort sU) as -> by admit. *)

    specialize (typed_preservation_eventually_invers_onestep 
      (insert_name x0 T0 ∅)
      e0 
      (fill K e1)
      H2 H2 
    ) as InvPreserve.
    edestruct InvPreserve as (e0'&e0''&A'&A''&HTye0''&(Hstepe0&Hnorme0)&(HstepA'&HnormA')).
    1: eapply fill_step;eassumption.


    exists (Lam x0 T0 f A'  e0').
    exists (Lam x0 T0 f A'' e0'').
    exists (Pi x0 T0 A').
    exists (Pi x0 T0 A'').
    split;[|split;split].
    1: {
      eapply typed_lam.
      1: eassumption. (* T did not change *)
      all: try eassumption. (* f did not change *)
      (* TODO: A'' is still typed with sort *)
      admit.
    }

    all: admit. (* easy *)

  - (* body of lambda *)

    edestruct (IHsyn_typed4) as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA&HNA)).
    2: eapply fill_step;eassumption.
    1: eassumption.

    exists (Lam x0 T0 f A'  Ke2').
    exists (Lam x0 T0 f A'' Ke2'').
    exists (Pi x0 T0 A').
    exists (Pi x0 T0 A'').
    split;[|split;split].
    2-5: admit. (* easy *)
    econstructor.
    all: try eassumption.
    admit. (* TODO: A'' still Sort typed *)
    

  - (* toplevel app *)

    assert(exists e2', e2 →ₙ e2') as [e2' He2'] by admit.
    specialize (typed_preservation_base_step _ _ _ _ _ HTy Hstep He2') as HTye2'.
    do 4 eexists.
    split. 2: split;split.
    1: eassumption.
    2: eassumption.
    1: constructor.
    1: constructor.
    admit. (* type already normalized (it is the result of normal_eval) *)

  - (* step in left app *)
    edestruct (IHsyn_typed1) as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA&HNA)). 
    1: assumption.
    1: eapply fill_step;eassumption.
    (* 
    TODO:
    the lambda domain type might make a step
    then the argument has to make steps

    or the body (and codomain) changes changing the complete type
     *)
     rename U' into substU.
     (* inversion on beta and normal *)
     assert(
      exists T' T'' U' U'',
      A' = Pi x T' U' /\ 
      T →ᵦ* T' /\ U →ᵦ* U' /\
      A'' = Pi x T'' U'' /\ 
      T' →ₙ T'' /\ U' →ₙ U''
     ) as  
     (
      T'&T''&U'&U''&
      HA'&
      HBT&HBU&
      HA''&
      HNT&HNU
     ) by admit.
     subst.
     (* the argument steps into an expression 
     of the correct type

     TODO: we want →ᵦ* and norm of the type not in exists
      *)
    specialize (typed_preservation_eventually_invers
      Γ
      v2 
      T
      H0 H0 
    ) as InvPreserve.
    edestruct InvPreserve as (v2'&v2''&T2'&T2''&HTyv2''&(Hstepv2&Hnormv2)&(HstepT2'&HnormT2')).
    1: eassumption.
    replace T2'' with T'' in * by admit. 
      (* 
      TODO:
      needs confluence? 
      but normalization complicated it
      => do we need beta norm steps and their confluence?
      *)




    (* assert (
      exists v2' v2'',
      TY ∅ ⊢ v2'' : T'' /\
      v2 →ᵦ* v2' /\ 
      v2' →ₙ v2''
    ) as (v2'&v2''&HTyv2&HBv2&HNv2) by admit. *)
    assert(
      exists substU'',
      subst' x v2'' U'' →ₙ substU''
    ) as (substU''&HsubstU'') by admit.
    exists (App Ke2' v2').
    exists (App Ke2'' v2'').
    exists (subst' x v2' U'). (* not correct instance *)
    (* exists (subst' x v2'' U'').  *)
    exists (substU''). 
    split;[|split;split].
    2,3,5: admit. (* easy *)
    2: admit. (* see comment => we have subst normal and want beta of that *)
    econstructor.
    1: eassumption.
    1: eassumption.
    1: eassumption.

    (*
    why does the normalized subst expression steps to something that is normalized into
    the required type
    => TODO: do we want to combine beta and normalization
    *)

    (* specialize (typed_preservation_eventually_invers 
      ∅
      v2
      T
      H0 H0 
    ) as InvPreserve.
    edestruct InvPreserve as (e0'&e0''&A'&A''&HTye0''&(Hstepe0&Hnorme0)&(HstepA'&HnormA')). *)



  - (* step in right app *)

    (*
      for e1 being a lambda, it would be easy 
      but e1 is no value
      => use if type steps, values steps

      but the type does (possibly) many steps

      ~~Problem: e0 might change its return type
      now we have the complicated situation with intermediate normalization~~

      e0 does not change its type (as e0 just follows the argument type reduction)
      The problem is that (see below in UB and UN)
    *)




    edestruct IHsyn_typed2 as (Ke2'&Ke2''&A'&A''&HTyKe2''&(HBKe2&HNKe2)&(HBA&HNA)). 
    1: assumption.
    1: eapply fill_step;eassumption.

    (* arg steps and lambda must reciprocate steps *)
    assert(Pi x T U →ᵦ* Pi x A' U) by admit. (* easy *)
    assert(Pi x A' U →ᵦ* Pi x A'' U) by admit. (* easy *)
    (* TODO: not exactly the type to expression lemma but instead multiple steps *)


    specialize (typed_preservation_eventually_invers
      _
      _ 
      _
      H H
    ) as InvPreserve.
    edestruct InvPreserve as (e0'&e0''&T2'&T2''&HTyv2''&(Hstepe0&Hnorme0)&(HstepT2'&HnormT2')).
    1: eassumption.

    (* TODO: confluence? Why exactly these beta steps *)
    assert (T2'' = Pi x A'' U) as -> by admit.

    (* assert(
      exists e0' e0'', 
      TY ∅ ⊢ e0'' : Pi x A'' U /\
      e0 →ᵦ* e0' /\ e0' →ₙ e0''
    ) as (e0'&e0''&HTye0&HBe0&HNe0) by admit. *)


    exists (App e0' Ke2').
    exists (App e0'' Ke2'').
    (* exists (subst' x (fill K e1) U). *)
    (* eexists. *)

    assert (exists UB UN,
      (* subst' x (fill K e1) U →ᵦ* UB /\ *)
      True /\
      UB →ₙ UN /\

      subst' x Ke2'' U →ₙ UN /\
      U' →ᵦ* UB
    ) as 
      (UB&UN&HBUB&HNU&HUN&HBU').
    {
      do 2 eexists.
      split;[|split;[|split]].
      3: admit. (* defining property of UN *)
      (* 
        UB can be subst x Ke2'' U with more or less normalization points
        e.g. subst x Ke2' U would be more points
        however, the normalized form (U') of subst x (fill K e1) U has to reduce to UB (3)
       *)
      3: admit.
      all: admit.
    }

    (* 
      subst' x (fill K e1) U →ᵦ* UB /\
      UB →ₙ UN

      subst' x Ke2'' U →ₙ UN
      (from eval typing)
      (uniquely determines UN)

      U' →ᵦ* UB
    *)

    (* assert (exists sUKe2,
      subst' x (Ke2'') U →ₙ sUKe2) as (sUKe2&HNsUKe2) by admit. *)
    (*
      we want just the beta steps in the normalized expression
      => need confluence?
    *)
    (*
    exists (subst' x (Ke2'') U). (* could be wrong instance *) 
    exists (sUKe2).
    *)
    exists UB.
    exists UN.
    split;[|split;split].
    1: {
      econstructor.
      all: try eassumption.
      (* admit.  *)
      (* subst already normalized (else normalize) *)
    }
    all: try eassumption.
    all: admit. (* easy *)
Admitted.


(*
typed_progress: typed expressions  are value or reducible
typed_preservation: typed expressions reduce eventually into a type expression

=> every typed expression eventually reduced into a typed value
(typed expressions don't get stuck)

or it loop infinitely
=> formulation if it terminates, it terminates in a well-typed value
*)




(* Lemma typed_safety e1 e2 A:
  TY ∅ ⊢ e1 : A →
  rtc contextual_step e1 e2 →
  is_val e2 ∨ reducible e2.
Proof.
  induction 2; eauto using typed_progress, typed_preservation.
Qed. *)
