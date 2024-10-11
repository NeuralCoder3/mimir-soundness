From stdpp Require Import base relations.
From iris Require Import prelude.
(* From thorin.lib Require Import maps. *)
From thorin Require Import lang notation.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Wf.
(* From Autosubst Require Export Autosubst. *)

(*
  Usually, typing uses deBrujin indices for naming
  this makes freshness, no-clash easy
  For deBrujin indices, Autosubst provides helpful lemmas and operations

  Our system is very similar to the calculus of construction
  as presented, for instance, in "Typed Lambda Calculus / Calculus of
Constructions" by Brandl
  (https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf)

  Our additions lie in the zip calculus (not discussed here for brevity),
  axioms (handled at this stage), and normalization.

  Our reduction goes under binder and evaluation also happens on type level.

  The most important difference to CC is that we have no rule that types can be beta equivalent for typing.
  Although we add such a rule for preservation (see below).
  Our normalization operations are applied eagerly at every construction and can be assumed as precondition for every expression.

  General idea:
  The proof is identical to normal CC progress and preservation proofs.
  Only normalization is added in between steps.
  In the inspected setting, normalization is a subset of beta steps.
*)

Definition typing_context := gmap string expr.
Implicit Types
  (Γ : typing_context)
  (e : expr).

Definition Star := Sort 0.
Definition insert_name (x: binder) (e: expr) (Γ: typing_context) :=
  match x with
  | BNamed x => <[x := e]> Γ
  | BAnon => Γ
  end.

(* instead of named and unnamed variants (as is common), we use insert_name to unify both into one *)
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

  We assume lemmas about renaming/name clash avoidance
*)
Axiom (subst_distr: forall x a e1 e2 e3,
  a ≠ x →
  subst a e1 (subst x e2 e3) = subst x (subst a e1 e2) (subst a e1 e3)).

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
One of our main lemmas:
Well typed expressions are not stuck
=> either step or are values

Progress 
|- e : A
=================
e is a value or
exists e' s.t. e -> e'
*)
Corollary typed_progress Γ e A:
  TY Γ ⊢ e : A →
  is_val e ∨ reducible e.
Proof.
  intros HTy.
  induction HTy.
  all: subst;eauto 10 using is_val.
  - (* Pi *)
    destruct IHHTy1 as [HvalT|[? ?]];[|right;eexists;eauto].
    destruct IHHTy2 as [HvalU|[? ?]];[|right;eexists;eauto].
    left. now constructor.
  - (* Lambda *)
    destruct IHHTy4 as [Hvale|[? ?]];[|right;eexists;eauto].
    destruct IHHTy2 as [HvalU|[? ?]];[|right;eexists;eauto].
    destruct IHHTy1 as [HvalT|[? ?]];[|right;eexists;eauto].
    left. now constructor.
  - (* App *)
    (* only value for Idx n *)
    destruct IHHTy1 as [Hvale|[? ?]];[|right;eexists;eauto].
    destruct IHHTy2 as [Hvale2|[? ?]];[|right;eexists;eauto].

    (*
    usually, we would have canonical values for Pi => lam or Idx: Nat -> Star
    and Nat => Lit
    Here, our application are more general (all non-redexes due to variables)
    *)
    destruct e.
    all: try now (left;constructor;eauto).
    right. eexists. 
    eapply base_contextual_step.
    eapply BetaS. reflexivity.
Qed.


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

Instead, we allow for the usual beta equivalence in types.

This way, our typing embeds: Every typed expression is also typed in "normal CC"
Then, a step preserves typing (modulo beta equivalence)
Hence, we end in a beta-equivalent type
For thorin's type fragment (e.g. finite termination on type level), the embed back works by normalization/furhter steps.

*)

Lemma fill_step K e1 e2:
  base_step e1 e2 ->
  fill K e1 →ᵦ fill K e2.
Proof.
  econstructor;eauto.
Qed.

















(*
just symmetry, refl, trans + (lam A. B) C = B [x := C]
or via beta reduction closure
*)
Definition equiv (A B:expr) := exists C, A →ᵦₙ* C ∧ B →ᵦₙ* C.
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
      (* 
      these are e1 ->n e1' and e2 ->n e2'
      do these need to be full to end normalizations? (probably?)
      => need to restrict full_contextual_steps to have normalized subexpression
       *)
      exists e1, e2.
      assert(
        normalized_pred e1 ∧ normalized_pred e2
      ) as [Hn1 Hn2].
      {
        inversion H4;subst.
        split.
        - apply norm_sound. constructor;eassumption.
        - apply norm_sound. eassumption.
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
    + subst;simpl in *.
      inversion H1;subst;clear H1.
      (* same as case above (go into right side instead of left) *)
      specialize (IHrtc e1 (full_fill K' e2')).
      edestruct IHrtc as [f1 [f2 [Hf1 [Hf2 [-> | [f' [Hstep Hnorm]]]]]]];eauto.
      1: constructor;eauto.
      * exists f1, f2. 
        split;[|split].
        1,3: eauto.
        destruct Hf2.
        constructor;eauto.
        econstructor.
        2: eassumption.
        econstructor;eauto.
      * exists f1, f2.
        split;[|split].
        1: assumption.
        1: {
          destruct Hf2.
          constructor;eauto.
          econstructor.
          2: eauto.
          econstructor;eauto.
        }
        right.
        exists f'. 
        split;eauto.
Qed.

Lemma normalized_norm_eval e e':
  normalized e →
  e →ₙ e' →
  e'=e.
Proof.
  intros Hnorm Hstep.
  destruct Hstep.
  apply norm_sound in Hnorm.
  inversion H;subst.
  - reflexivity.
  - unfold normalized_pred in Hnorm.
    contradict Hnorm.
    eexists;eassumption.
Qed.

  (*
  we have a unique normal form of expressions
  => 
  - if go into one subexpression, we eventuelly go in the other (as we do all redexes)
  - if doing toplevel step, it does not matter if we normalized the subst-in argument before or after
  *)
Lemma normalized_unique e e'1 e'2:
  e →ₙ e'1 →
  e →ₙ e'2 →
  e'1 = e'2.
Proof.
Admitted.


Lemma normalize_pi x T U e'_norm:
  Pi x T U →ₙ e'_norm ->
  exists T' U',
  e'_norm = Pi x T' U' /\
  normal_eval T T' /\
  normal_eval U U'.
Proof.
  intros [Hstep Hnorm%norm_sound2].
  dependent induction Hstep.
  - inversion Hnorm;subst.
    do 2 eexists. firstorder.
    1,3: reflexivity.
    all: now apply norm_sound.
  - inversion H;subst.
    destruct K;simpl in *;inversion H0;subst.
    1: {inversion H2. }
    1: specialize (IHHstep x0 (full_fill K e2') U0).
    2: specialize (IHHstep x0 K (full_fill K0 e2')).
    all: destruct IHHstep as (T'&U'&->&[HTs HTn]&[HUs HUn]);eauto.
    all: do 2 eexists;firstorder.
    all: econstructor;eauto;econstructor;eauto.
Qed.

Lemma sort_subst_inv a e s:
  subst' a e (Sort s) = Sort s.
Proof.
  now destruct a.
Qed.

Lemma sort_norm s:
  Sort s →ₙ Sort s.
Proof.
  econstructor.
  - econstructor.
  - apply norm_sound;constructor.
Qed.


(*
R v k = normal_eval f k
f v = subst' a e'
*)
Definition gamma_relation Γ Γ' R :=
  forall x v,
    Γ !! x = Some v <-> (exists k, Γ' !! x = Some k /\ R v k).

Lemma Gamma_insert_property Γ Γ' (R:expr->expr->Prop) x T T':
  R T T' ->
  gamma_relation Γ Γ' R ->
  gamma_relation (insert_name x T Γ) (insert_name x T' Γ') R.
Proof.
  intros HR HΓ y v.
  destruct x;simpl in *.
  1:{
    unfold gamma_relation in HΓ.
    apply HΓ.
  }
  split.
  - intros H.
    edestruct (lookup_insert_Some Γ).
    apply H0 in H;clear H0 H1.
    unfold gamma_relation in HΓ.
    destruct H as [[-> ->]|[]].
    + exists T'.
      split;eauto.
      rewrite lookup_insert;eauto.
    + edestruct HΓ.
      apply H1 in H0 as [k [Hk HRk]].
      eexists;split;eauto.
      rewrite lookup_insert_ne;eauto.
  - edestruct HΓ.
    intros [k [Hk HRk]].
    destruct (decide (s = y)) as [->|Hneq].
    + rewrite lookup_insert in Hk.
      rewrite lookup_insert.
      f_equal.
      inversion Hk;subst.
      shelve.
    + rewrite lookup_insert_ne in Hk;eauto.
      rewrite lookup_insert_ne;eauto.
Admitted.


Lemma normalize_lam x T ef U e e'_norm:
  Lam x T ef U e →ₙ e'_norm ->
      exists T' U' ef' e'',
      e'_norm = Lam x T' ef' U' e'' /\
      normal_eval T T' /\
      normal_eval ef ef' /\
      normal_eval U U'.
Proof.
  intros [Hstep Hnorm%norm_sound2].
  dependent induction Hstep.
  - inversion Hnorm;subst.
    do 4 eexists. 
    firstorder.
    1,3,5: reflexivity.
    all: now apply norm_sound.
  - inversion H;subst.
    destruct K;simpl in *;inversion H0;subst.
    1: {inversion H2. }
    1: specialize (IHHstep x0 (full_fill K e2') f U0 e0).
    2: specialize (IHHstep x0 T0 (full_fill K e2') U0 e0).
    3: specialize (IHHstep x0 T0 f (full_fill K e2') e0).
    4: specialize (IHHstep x0 T0 f U0 (full_fill K e2')).
    all: destruct IHHstep as (T'&U'&ef'&e''&->&[HTs HTn]&[Hefs Hefn]&[HUs HUn]);eauto.
    all: do 4 eexists;firstorder.
    all: econstructor;eauto;econstructor;eauto.
Qed.

Lemma subst'_bot a e:
  subst' a e Bot = Bot.
Proof.
  destruct a;reflexivity.
Qed.

Lemma norm_bot e:
  Bot →ₙ e ->
  e = Bot.
Proof.
  intros H%normalized_norm_eval;eauto.
  econstructor.
Qed.


(*
prepend normal steps do not change the normalization
after all, all our expressions are normalized
*)
Lemma norm_beta_preserve A B A' B':
  A ≡ᵦ B ->
  A →ₙ A' ->
  B →ₙ B' ->
  A' ≡ᵦ B'.
Proof.
Admitted.

(*
simple except app -> normalize again after beta step
=> user has to guarantee finite normalization chains
*)
Lemma normal_functional e:
  {e' | normal_eval e e'}.
Proof.
  induction e.  
  1-7: eexists;subst;constructor;[constructor|];apply norm_sound;constructor.
  - destruct IHe1 as [e1' [He1' Hnorme1']].
    destruct IHe2 as [e2' [He2' Hnorme2']].
    exists (Pi x e1' e2').
    constructor.
    + eapply rtc_rtc.
      * eapply rtc_full_contextual_context.
        -- apply He1'.
        -- instantiate (1:=(FPi1 x FHoleCtx e2));simpl;reflexivity.
        -- simpl. reflexivity.
      * eapply rtc_full_contextual_context.
        -- apply He2'.
        -- instantiate (1:=(FPi2 x e1' FHoleCtx));simpl;reflexivity.
        -- simpl. reflexivity.
    + apply norm_sound.
      constructor;auto.
      all: now apply norm_sound2.
  - destruct IHe1 as [e1' [He1' Hnorme1']].
    destruct IHe2 as [e2' [He2' Hnorme2']].
    destruct IHe3 as [e3' [He3' Hnorme3']].
    destruct IHe4 as [e4' [He4' Hnorme4']].
    exists (Lam x e1' e2' e3' e4').
    constructor.
    + eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FLam1 x FHoleCtx e2 e3 e4);[apply He1'| |];simpl;reflexivity.
      eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FLam2 x e1' FHoleCtx e3 e4);[apply He2'| |];simpl;reflexivity.
      eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FLam3 x e1' e2' FHoleCtx e4);[apply He3'| |];simpl;reflexivity.
      eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FLam4 x e1' e2' e3' FHoleCtx);[apply He4'| |];simpl;reflexivity.
      constructor.
    + apply norm_sound.
      constructor;auto.
      all: now apply norm_sound2.
  - destruct IHe1 as [e1' [He1' Hnorme1']].
    destruct IHe2 as [e2' [He2' Hnorme2']].
    assert(rtc full_contextual_step (App e1 e2) (App e1' e2')).
    {
      eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FApp1 FHoleCtx e2);[apply He1'| |];simpl;reflexivity.
      eapply rtc_rtc.
      1: eapply rtc_full_contextual_context with (K:=FApp2 e1' FHoleCtx);[apply He2'| |];simpl;reflexivity.
      constructor.
    }
Admitted.


Lemma subst_expression_norm_type Γ x e' A Γ' e'_norm B'_norm:
  TY Γ ⊢ᵦ e' : A ->
  e' →ₙ e'_norm ->
  subst x e' A →ₙ B'_norm ->
  gamma_relation Γ Γ' (λ v k : expr, subst x e' v →ₙ k) ->
  TY Γ' ⊢ᵦ e'_norm : B'_norm.
Proof.
  assert (subst x e' A = A) as HsubstA by admit. (* avoid name clash *)
  rewrite HsubstA.
Admitted.

Lemma beta_typed_substitutivity e e' Γ (a: binder) A B 
  Γ' e'_norm B'_norm:
  TY Γ ⊢ᵦ e' : A →
  TY (insert_name a A Γ) ⊢ᵦ e : B →
  normal_eval (lang.subst' a e' e) e'_norm →
  normal_eval (lang.subst' a e' B) B'_norm →
  (* (forall x v,
    Γ !! x = Some v <-> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k)) -> *)
    (* /\ Γ' !! x = Some v -> (exists k, Γ' !! x = Some k /\ normal_eval (subst' a e' v) k) -> *)
  gamma_relation Γ Γ' (fun v k => normal_eval (subst' a e' v) k) ->
  TY Γ' ⊢ᵦ e'_norm : B'_norm.
Proof.
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
    replace e'_norm with Bot by (rewrite subst'_bot in Hnorme;now apply norm_bot in Hnorme).
    replace B'_norm with Star.
    2: {
      replace (subst' a e' Star) with Star in HnormB by now destruct a.
      now apply normalized_norm_eval in HnormB;[|econstructor].
    }
    econstructor.
  - (* Nat *)
    replace e'_norm with Nat.
    2: {
      replace (subst' a e' Nat) with Nat in Hnorme by now destruct a.
      now apply normalized_norm_eval in Hnorme;[|econstructor].
    }
    replace B'_norm with Star.
    2: {
      replace (subst' a e' Star) with Star in HnormB by now destruct a.
      now apply normalized_norm_eval in HnormB;[|econstructor].
    }
    econstructor.
  - (* Idx *)
    replace e'_norm with Idx.
    2: {
      replace (subst' a e' Idx) with Idx in Hnorme by now destruct a.
      now apply normalized_norm_eval in Hnorme;[|econstructor].
    }
    replace B'_norm with (Pi BAnon Nat Star).
    2: {
      replace (subst' a e' (Pi BAnon Nat Star)) with (Pi BAnon Nat Star) in HnormB by now destruct a.
      apply normalized_norm_eval in HnormB;[easy|];repeat constructor.
    }
    econstructor.
  - (* LitNat *)
    replace e'_norm with (#n)%E.
    2: {
      replace (subst' a e' (#n)%E) with (#n)%E in Hnorme by now destruct a.
      now apply normalized_norm_eval in Hnorme;[|econstructor].
    }
    replace B'_norm with Nat.
    2: {
      replace (subst' a e' Nat) with Nat in HnormB by now destruct a.
      now apply normalized_norm_eval in HnormB;[|econstructor].
    }
    econstructor.
  - (* LitIdx *)
    replace e'_norm with (LitIdx n i).
    2: {
      replace (subst' a e' (LitIdx n i)) with (LitIdx n i) in Hnorme by now destruct a.
      now apply normalized_norm_eval in Hnorme;[|econstructor].
    }
    replace B'_norm with (App Idx n).
    2: {
      replace (subst' a e' (App Idx n)) with (App Idx n) in HnormB by now destruct a.
      apply normalized_norm_eval in HnormB;[easy|];repeat constructor.
      intros (?&?&?&?&?&[H ->]).
      inversion H.
    }
    econstructor.
  - (* Var *)
    (*
      if not subst => all same => no problem
    *)
    assert (a=BAnon \/ a = BNamed x \/ (exists y, a = BNamed y ∧ y ≠ x)) as [->|[->|[y [-> Hne]]]]. 
    {
      destruct a;[now left|right].
      destruct (decide (s = x)).
      - left. now subst.
      - right. exists s. split;[easy|]. intros ->. congruence.
    }
    + simpl in *.
      replace e'_norm with (Var x).
      2: {
        now apply normalized_norm_eval in Hnorme;[|econstructor].
      }
      econstructor.
      edestruct HΓ.
      apply H0 in H as [? []].
      specialize (normalized_unique _ _ _ HnormB H2) as ->.
      apply H.
    + replace (subst' x e' x) with e' in Hnorme by (simpl;destruct decide;congruence).
      simpl in *.
      (* This is: replace A0 with A in *. *)
      rewrite lookup_insert in H.
      inversion H;subst.
      eapply subst_expression_norm_type;eauto.
    + replace (subst' y e' x) with (Var x) in Hnorme by (simpl;destruct decide;congruence).
      replace e'_norm with (Var x).
      2: now apply normalized_norm_eval in Hnorme;[|econstructor].
      simpl in *.
      rewrite lookup_insert_ne in H;[|assumption].
      edestruct HΓ.
      apply H0 in H as [? []].
      econstructor.
      specialize (normalized_unique _ _ _ HnormB H2) as ->.
      assumption.
  - (* Pi *)
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in Hnorme.
    2: {
      destruct a; simpl.
      - reflexivity.
      - f_equal.
        admit. (* no overlap => binder is not x *)
    }
    assert(
      exists T' U',
      e'_norm = Pi x T' U' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [He'_norm [HnormT HnormU]]]] by now apply normalize_pi.
    subst.
    simpl in HnormB.
    replace (B'_norm) with (LitNat(max sT sU)).
    2: {
      replace (subst' a e' (LitNat(max sT sU))) with (LitNat(max sT sU)) in HnormB by now destruct a.
      now apply normalized_norm_eval in HnormB;[|econstructor].
    }
    econstructor.
    + eapply IHbeta_syn_typed1.
      3: eapply HnormT.
      3: rewrite sort_subst_inv;now apply sort_norm.
      1: eassumption.
      reflexivity.
      eassumption.
    + eapply IHbeta_syn_typed2 with (Γ := insert_name x T Γ).
      3: eassumption.
      3: rewrite sort_subst_inv;now apply sort_norm.
      1: admit. (* x not free in e' => no overlap *)
      1: admit. (* different order insert *)
      apply Gamma_insert_property;eauto.
  - (* Lambda *)
    replace (subst' a e' (Lam x T ef U e)) with (Lam x (subst' a e' T) (subst' a e' ef) (subst' a e' U) (subst' a e' e)) in Hnorme. 
    2: {
      destruct a;simpl;eauto.
      f_equal.
      all: destruct decide;eauto.
      all: admit. (* no overlap *)
    }
    pose proof HnormB as HnormB2.
    replace (subst' a e' (Pi x T U)) with (Pi x (subst' a e' T) (subst' a e' U)) in HnormB2.
    2: {
      destruct a;simpl;eauto.
      f_equal.
      all: destruct decide;eauto.
      all: admit. (* no overlap *)
    }
    assert(
      exists T' U' ef' e'',
      e'_norm = Lam x T' ef' U' e'' /\
      normal_eval (subst' a e' T) T' /\
      normal_eval (subst' a e' ef) ef' /\
      normal_eval (subst' a e' U) U'
    ) as [T' [U' [ef' [e'' [He'_norm [HnormT [Hnormef HnormU]]]]]]] by now apply normalize_lam in Hnorme.
    subst.
    assert(
      exists T'' U'',
      B'_norm = Pi x T'' U'' /\
      normal_eval (subst' a e' T) T'' /\
      normal_eval (subst' a e' U) U''
    ) as [T'' [U'' [HB'_norm [HnormT' HnormU']]]] by now apply normalize_pi.
    subst.
    (* confluence of normalize *)
    assert (T' = T'') as -> by now eapply normalized_unique with (e:=subst' a e' T) in HnormT;[|eauto].
    assert (U' = U'') as -> by now eapply normalized_unique with (e:=subst' a e' U) in HnormU;[|eauto].
    econstructor.
    + eapply IHbeta_syn_typed1.
      2-5: try eassumption.
      1-2: eauto.
      replace (subst' a e' (Sort sT)) with (Sort sT) by now destruct a.
      constructor;[constructor|apply norm_sound;constructor].
    + eapply IHbeta_syn_typed2 with (Γ := insert_name x T Γ).
      3: eassumption.
      1: admit. (* no overlap *)
      1: admit. (* insert order *)
      1: {
        destruct a;simpl;constructor.
        1,3: reflexivity.
        all: apply norm_sound;constructor.
      }
      apply Gamma_insert_property;eauto.
    + eapply IHbeta_syn_typed3 with (Γ := insert_name x T Γ); eauto.
      2: admit. (* insert order *)
      3: apply Gamma_insert_property;eauto.
      2: {
        replace (subst' a e' Bool) with Bool by now destruct a.
        constructor;[reflexivity|(apply norm_sound;constructor)].
        1,2: constructor.
        intros (?&?&?&?&?&[? ->]). inversion H3.
      }
      admit. (* no overlap *)
    + admit. (* same as two cases above *)
  - (* App *)
    (* norm can beta or just norm in subterms *)
    replace(subst' a e' (e eT)) with ((subst' a e' e) (subst' a e' eT)) in Hnorme.
    2: {
      destruct a; simpl;reflexivity.
    }
    apply app_norm in Hnorme as [e1' [e2' [Hstep1 [Hstep2 [->|[enorm [? ?]]]]]]].
    + eapply beta_typed_app.
      * eapply IHbeta_syn_typed1;eauto. admit. (* Pi normalized to Pi *)
      * eapply IHbeta_syn_typed2;eauto. admit. (* type norm *)
      * admit. (* e2' instead of e' in subst => normalization distributes subst *)
    + specialize (IHbeta_syn_typed1 _ _ _ He' eq_refl).
      specialize (IHbeta_syn_typed2 _ _ _ He' eq_refl).
      admit. (* normalization of subst *)
  - (* beta case *)
    specialize (IHbeta_syn_typed Γ a A He' eq_refl).
    (*
    generalize over A0?
    allow for more beta equiv?
    convert type of e by rule?
      => we have e: B (not needed)
      => we need subst A0 -> B'_norm (does not hold (only beta equiv))
    convert goal by conv rule?
      we have e'_norm : A0_subst_norm 
      => need A0_subst_norm equiv B'_norm
    *)
    assert(exists A0',
      subst' a e' A0 →ₙ A0'
    ) as [A0' HnormA0].
    {
      edestruct normal_functional.
      eexists. eauto.
    }
    assert (A0' ≡ᵦ B'_norm) as Hconv.
    {
      eapply norm_beta_preserve.
      2, 3: eassumption.
      admit.
      (*
        if A0 equiv B
        then 
        subst a e' A0 equiv subst a e' B

        => beta equiv of subst preservation
      *)
    }
    eapply beta_typed_conv;[|eassumption].
    eapply IHbeta_syn_typed;eauto.
Admitted.

Definition gamma_step Γ Γ' :=
  exists x v v',
    Γ !! x = Some v /\
    Γ' !! x = Some v' /\
    (forall y, y ≠ x -> Γ !! y = Γ' !! y) /\
    v →ᵦₙ v'.

Lemma extend_gamma_step x v Γ Γ':
  gamma_step Γ Γ' ->
  gamma_step (insert_name x v Γ) (insert_name x v Γ').
Proof.
  intros H.
  destruct x;simpl;eauto.
  destruct H as [y [v0 [v1 [HΓ [HΓ' [HOther Hstep]]]]]].
  destruct (decide (s = y)).
  - admit. (* avoid name clash *)
  - eexists y, v0, v1.
    repeat split;eauto.
    1,2: rewrite lookup_insert_ne;eauto.
    intros z Hneq.
    destruct (decide (z = s));subst.
    + do 2 rewrite lookup_insert;eauto.
    + do 2 (rewrite lookup_insert_ne;eauto).
Admitted.

Lemma insert_gamma_step x v v' Γ:
  v →ᵦₙ v' ->
  gamma_step (<[x:=v]>Γ) (<[x:=v']>Γ).
Proof.
  intros.
  eexists x, v, v'.
  repeat rewrite lookup_insert.
  repeat split;eauto.
  intros.
  rewrite lookup_insert_ne;eauto.
  rewrite lookup_insert_ne;eauto.
Qed.

Lemma insert_name_gamma_step x v v' Γ:
  v →ᵦₙ v' ->
  gamma_step (insert_name x v Γ) (insert_name x v' Γ).
Admitted.

Lemma step_equiv e e':
  e →ᵦₙ e' ->
  e ≡ᵦ e'.
Admitted.

Lemma equiv_symmetry e1 e2:
  e1 ≡ᵦ e2 ->
  e2 ≡ᵦ e1.
Proof.
  intros (e'&H1&H2).
  exists e';now split.
Qed.

Lemma beta_fill_step K e1 e2 e':
base_step e1 e2 ->
fill K e2 →ₙ e' ->
fill K e1 →ᵦₙ e'.
Proof.
  intros.
  econstructor;split.
  2: eassumption.
  now econstructor.
Qed.

#[global]
Hint Resolve insert_name_gamma_step beta_fill_step : core.

Lemma step_beta_preservation Γ e A:
  TY Γ ⊢ᵦ e : A ->
  (forall e', e →ᵦₙ e' ->
  TY Γ ⊢ᵦ e' : A) /\
  (forall Γ', gamma_step Γ Γ' ->
  TY Γ' ⊢ᵦ e : A)
  .
Proof.
  intros HTy.
  dependent induction HTy;(split;
    [
      intros e' [e'' [[K e1 e2 ? ? Hstep] Hnorm]];subst|
      intros Γ' Hstep
    ]).
  all: try now (destruct K;cbn in *;inversion Hstep;subst).
  all: try now constructor.
  2,4,6,8: shelve.
  - destruct Hstep as (y&v&v'&HΓ&HΓ'&HOther&Hstep).
    destruct (decide (x = y));subst.
    + rewrite H in HΓ. inversion HΓ;subst.
      eapply beta_typed_conv.
      * econstructor; eassumption.
      * now apply equiv_symmetry,step_equiv.
    + constructor.
      rewrite <- H. symmetry.
      now apply HOther.
  - constructor.
    + apply IHHTy1;assumption.
    + apply IHHTy2. 
      apply extend_gamma_step. assumption.
  - econstructor;eauto.
    + now apply IHHTy1.
    + apply IHHTy2. now apply extend_gamma_step.
    + apply IHHTy3. now apply extend_gamma_step.
    + apply IHHTy4. now apply extend_gamma_step.
  - econstructor;eauto.
    + now apply IHHTy1.
    + now apply IHHTy2. 
  - econstructor;eauto.
    now apply IHHTy.

  Unshelve.
  { (* Pi *)
    destruct K;cbn in *;inversion H;subst.
    + inversion Hstep.
    + (* step in Type *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Pi x0 Ke2' U0
      ) as [Ke2' [HKe2norm ->]].
      {
        apply normalize_pi in Hnorm as [T' [U' [-> [HT HU]]]].
        eexists;split;eauto.
        admit. (* U0 is U' as it is already normalized *)
      }
      eapply beta_typed_pi.
      * eapply IHHTy1. 
        eapply beta_fill_step;eauto.
      * (* step in context *)
        apply IHHTy2.
        apply insert_name_gamma_step.
        eapply beta_fill_step;eauto.
    + (* step in codom *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Pi x0 T0 Ke2'
      ) as [Ke2' [HKe2norm ->]].
      {
        apply normalize_pi in Hnorm as [T' [U' [-> [HT HU]]]].
        eexists;split;eauto.
        admit. (* T0 is T' as it is already normalized *)
      }
      eapply beta_typed_pi.
      * eassumption.
      * eapply IHHTy2;eapply beta_fill_step;eauto.
  }
  { (* Lam *)
    destruct K;cbn in *;inversion H;subst.
    + inversion Hstep.
    + (* step in Type *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x0 Ke2' f U0 e0
      ) as [Ke2' [HKe2norm ->]]. 
      {
        apply normalize_lam in Hnorm as [T' [U' [f' [e'' [-> [HT [Hf [HU]]]]]]]].
        eexists;split;eauto.
        admit. (* e0=e', U0=U' as it is already normalized *)
      }
      eapply beta_typed_conv.
      eapply beta_typed_lam.
      * eapply IHHTy1;eauto.
      * apply IHHTy2;eauto.
      * apply IHHTy3;eauto.
      * apply IHHTy4;eauto.
      * admit. (* Beta *)
    + (* step in codom *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x0 T0 f Ke2' e0
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_conv.
      eapply beta_typed_lam;eauto.
      * apply IHHTy2;eauto.
      * eapply beta_typed_conv.
        1: eassumption.
        admit. (* beta conversion *)
      * admit. (* beta conversion *)
    + (* body *)
      assert (
        exists Ke2',
        fill K e2 →ₙ Ke2' /\
        e' = Lam x0 T0 f U0 Ke2'
      ) as [Ke2' [HKe2norm ->]] by admit.
      eapply beta_typed_lam;eauto. 
      apply IHHTy4;eauto.
  }
  { (* App *)
    destruct K;cbn in *;inversion H0;subst.
    (* case left *)
    2: {
      assert(exists Ke2',
        fill K e2 →ₙ Ke2'
      ) as [Ke2' HKe2norm].
      {
        edestruct normal_functional.
        eexists; eauto.
      }
      assert (TY Γ ⊢ᵦ Ke2' v2 : U') as Hty.
      {
        eapply beta_typed_app.
        - eapply IHHTy1;eauto.
        - eauto.
        - eauto.
      }
      (* if normalization of toplevel redex => done *)

      (* just case distinction on normalization *)
      (*
        e1 e2 ->n en
        e1 ->n e1n
        e2 ->n e2n

        en = e1n e2n \/ e1n e2n toplevel normalize to en' and en' ->n en
      *)

      idtac.
      assert (normalize_step (App Ke2' v2) e') as Hstep' by admit. (* combination of norm steps *)
      inversion Hstep';subst.
      rename eb into elam.

      (* inversion Hstep';subst. *)
      pose proof beta_typed_substitutivity.
      specialize (H1 elam v2 Γ x0).
      specialize (H1 T).
      assert(TY (insert_name x0 T Γ) ⊢ᵦ elam : U0) as Htyelam by admit.
      (* assert (x=x0) as ->.  {
        inversion HTy1;eauto.
        admit.
      } *)
      specialize (H1 U0 Γ).

      inversion Hty;subst.
      2: {
        admit. (* subst in elam is typed *)
      }
      eapply H1;eauto.
      + admit. (* subst on normalized values is normalized *)
      + inversion H8;subst.
        2: { admit. } (* beta conversion case *)
        assumption.
      + admit. (* gamma relation *)
    }
    (* case right *)
    2: {
      assert(exists Ke2',
        fill K e2 →ₙ Ke2'
      ) as [Ke2' HKe2norm] by (edestruct normal_functional;eauto).
      assert (exists Ue2', subst' x Ke2' U →ₙ Ue2') as [Ue2' HUe2norm] by (edestruct normal_functional;eauto).
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
    inversion Hstep;subst.
    pose proof beta_typed_substitutivity.
    specialize (H0 elam eT Γ x).
    specialize (H0 T).
    assert (x=x0) as ->.  {
      inversion HTy1;subst;eauto.
      admit. (* type conversion case *)
    }
    assert(TY (insert_name x0 T Γ) ⊢ᵦ elam : U) as Htyelam. 
    {
      (* clear H H0 Hstep H1 Hnorm IHHTy1 IHHTy2 HTy2. *)
      inversion HTy1;subst.
      2: {
        admit.  (* type conversion case => *)
      }
      assumption.
    }
    specialize (H0 U Γ e').
    eapply H0;eauto.
    admit. (* subst does not change expressions *)
  } 
  { (* equiv *)
    eapply beta_typed_conv.
    1: {
      eapply IHHTy; eauto.
    }
    assumption.
  }
Admitted.


Corollary beta_preservation Γ e A e':
  TY Γ ⊢ᵦ e : A ->
  e →ᵦₙ e' ->
  TY Γ ⊢ᵦ e' : A.
Proof.
  intros [H ?]%step_beta_preservation.
  now apply H.
Qed.

