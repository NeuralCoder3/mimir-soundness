From stdpp Require Export binders strings.
From iris.prelude Require Import options.
From thorin.lib Require Export maps.
Require Import Coq.Program.Equality.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Inductive expr :=
  | Sort (n:nat)
  | Bot
  | Nat
  | Idx 
  | LitNat (n : nat)
  | LitIdx (n : nat) (i:Fin.t n)
  | Var (x : string)
  (* let is already normalized *)
  (* axiom is already handled *)
  | Pi (x : binder) (T U : expr)
  | Lam (x : binder) (T : expr) (f : expr) (U: expr) (e: expr)
  | App (e1 e2 : expr)
.

Bind Scope expr_scope with expr.


Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  let recurse_under y expr := if decide (y = BNamed x) then expr else subst x es expr in
  match e with
  | Sort _ | Bot | Nat | Idx | LitNat _ | LitIdx _ _  => e
  | Var y => if decide (y = x) then es else e
  (* replace x in T, replace in U if not x *)
  | Pi y T U => 
    Pi y (subst x es T) (recurse_under y U)
  (* replace x in T, f, U, and e only if not x *)
  | Lam y T f U e => 
    Lam y (subst x es T) 
      (recurse_under y f)
      (recurse_under y U)
      (recurse_under y e)
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.


Lemma fin_inc n (i:Fin.t n): (` (Fin.to_nat (Fin.FS i))) = S (` (Fin.to_nat i)).
Proof.
  simpl.
  now destruct Fin.to_nat.
Defined.

Lemma nth_fin A (xs:list A) (i:Fin.t (length xs)) :
  exists x, nth_error xs (` (Fin.to_nat i)) = Some x.
Proof.
  induction xs;simpl in *.
  - inversion i.
  - dependent inversion i;subst.
    + now exists a.
    + specialize (IHxs t) as [x H].
      exists x.
      rewrite <- H.
      now rewrite fin_inc.
Qed.

(*
  enumerate all fin numbers up to n
  then map over the list with subst
*)
Definition fin_list (n:nat) : 
  {xs : list (Fin.t n) | 
    length xs = n /\ 
    (forall (i:Fin.t n), nth_error xs (` (Fin.to_nat i)) = Some i)
  }.
  induction n.
  - exists []. split; auto.
    intros i. inversion i.
  - destruct IHn as [xs [Hlen Hnth]].
    exists (Fin.F1 :: map (fun i => Fin.FS i) xs);split.
    + simpl. f_equal. 
      now rewrite map_length.
    + intros i.
      dependent destruction i.
      * reflexivity.
      * rewrite fin_inc.
        simpl.
        now apply map_nth_error.
Defined.

(* instantiate e via subst with x = LitIdx n 0 ... ListIdx (n-1) *)
Definition instantiate (x:string) (n:nat) (e:expr) : list expr.
  destruct (fin_list n) as [xs [Hlen Hnth]].
  refine (map (fun i => subst x (LitIdx n i) e) xs).
Defined.

Corollary instantiate_correct x n e:
  forall i, nth_error (instantiate x n e) (` (Fin.to_nat i)) = Some (subst x (LitIdx n i) e).
Proof.
  unfold instantiate.
  destruct (fin_list n) as [xs [Hlen Hnth]].
  intros i.
  change (subst x (LitIdx n i) e) with ((fun i => subst x (LitIdx n i) e) i).
  now apply map_nth_error.
Qed.


Definition Bool := App Idx (LitNat 2).
Definition ETrue := LitIdx 2 (Fin.FS Fin.F1).

Inductive normalized : expr -> Prop :=
  (* atomic values *)
  (* conceptually, every value is normalized (not quite -- normalization goes under binders) *)
  (* but for distinction, differences and adaptation, we should keep normalization without is_val *)
  | norm_Sort n: normalized (Sort n)
  | norm_Bot: normalized Bot
  | norm_Nat: normalized Nat
  | norm_Idx: normalized Idx
  | norm_LitNat n: normalized (LitNat n)
  | norm_LitIdx n i: normalized (LitIdx n i)
  | norm_Var x: normalized (Var x)
  (* congruence rules *)
  | norm_Pi x T U: normalized T -> normalized U -> normalized (Pi x T U)
  | norm_Lam x T f U e: normalized T -> normalized f -> normalized U -> normalized e -> normalized (Lam x T f U e)

  (*
    App
    - subexpressions normalized 
    - not beta redex with true filter
  *)
  | norm_App e1 e2:
    normalized e1 -> normalized e2 -> 
    ~(exists x T f U e, e1 = Lam x T f U e /\ f = ETrue) ->
    normalized (App e1 e2)
  .


Inductive normalize_step : expr -> expr -> Prop :=
  | normalize_beta x T ef U eb ea:
    ef = ETrue ->
    normalized T ->
    normalized U ->
    normalized ef ->
    normalized eb ->
    normalized ea ->
    normalize_step (App (Lam x T ef U eb) ea) (subst' x ea eb)
.

Inductive full_ectx :=
  | FHoleCtx
  | FPi1 (x:binder) (K: full_ectx) (U:expr)
  | FPi2 (x:binder) (K: expr) (U:full_ectx)
  | FLam1 (x:binder) (T: full_ectx) (f:expr) (U:expr) (e:expr)
  | FLam2 (x:binder) (T: expr) (f:full_ectx) (U:expr) (e:expr)
  | FLam3 (x:binder) (T: expr) (f:expr) (U:full_ectx) (e:expr)
  | FLam4 (x:binder) (T: expr) (f:expr) (U:expr) (e:full_ectx)
  | FApp1 (K: full_ectx) (e2 : expr)
  | FApp2 (e1 : expr) (K: full_ectx)
  .

Fixpoint full_fill (K:full_ectx) (e:expr) : expr :=
  match K with
  | FHoleCtx => e
  | FPi1 x K U => Pi x (full_fill K e) U
  | FPi2 x T K => Pi x T (full_fill K e)
  | FLam1 x K f U eb => Lam x (full_fill K e) f U eb
  | FLam2 x T K U eb => Lam x T (full_fill K e) U eb
  | FLam3 x T f K eb => Lam x T f (full_fill K e) eb
  | FLam4 x T f U K  => Lam x T f U (full_fill K e)
  | FApp1 K e2 => App (full_fill K e) e2
  | FApp2 e1 K => App e1 (full_fill K e)
  end.

Fixpoint comp_full_ectx (K1 K2: full_ectx) :=
  match K1 with 
  | FHoleCtx => K2
  | FPi1 x K U => FPi1 x (comp_full_ectx K K2) U
  | FPi2 x T K => FPi2 x T (comp_full_ectx K K2)
  | FLam1 x K f U eb => FLam1 x (comp_full_ectx K K2) f U eb
  | FLam2 x T K U eb => FLam2 x T (comp_full_ectx K K2) U eb
  | FLam3 x T f K eb => FLam3 x T f (comp_full_ectx K K2) eb
  | FLam4 x T f U K  => FLam4 x T f U (comp_full_ectx K K2)
  | FApp1 K e2 => FApp1 (comp_full_ectx K K2) e2
  | FApp2 e1 K => FApp2 e1 (comp_full_ectx K K2)
  end.

Lemma full_fill_comp K1 K2 e:
  full_fill (comp_full_ectx K1 K2) e = full_fill K1 (full_fill K2 e).
Proof. induction K1; simpl; congruence. Qed.

Inductive full_contextual_step (e1 : expr) (e2 : expr) : Prop :=
  (* by the definition of normalize_step, the subexpressions are already normalized
    enforcing full normalization from bottom up
  *)
  Fectx_step K e1' e2' :
    e1 = full_fill K e1' → e2 = full_fill K e2' →
    normalize_step e1' e2' → full_contextual_step e1 e2.

(*
Due to indirection, a inductive definition is not possible
This version (using ~∃) is a pain to work with.
We will usually use the constructive inductive predicate
but this formulation is more direct / related to the code
*)
Definition normalized_pred (e : expr) :=
  ~ ∃ e', full_contextual_step e e'.

(* perform all possible normalization redexes *)
Definition normal_eval e e' :=
  rtc full_contextual_step e e' ∧ normalized_pred e'.

(* 
  we define is_val for normalized expressions => does not contain a beta redex
  applications are not values
*)
Definition is_lam (e:expr) :=
  match e with
  | Lam _ _ _ _ _ => True
  | _ => False
  end.
Inductive is_val : expr → Prop :=
  (* progress in CC needs to talk about vars *)
  (* we do not have canonical values directly as we need vars as values *)
  | VarV x : is_val (Var x) 
  | AppV v1 v2: 
    ~is_lam v1 →
    is_val v1 → is_val v2 → is_val (App v1 v2)
  | SortV n : is_val (Sort n)
  | BotV : is_val Bot
  | NatV : is_val Nat
  | IdxV : is_val Idx
  | IdxAppV n : is_val (App Idx (LitNat n))
  | LitNatV n : is_val (LitNat n)
  | LitIdxV n i : is_val (LitIdx n i)
  | PiV x T U : 
    is_val T →
    is_val U →
    is_val (Pi x T U)
  | LamV x T f U e : 
    is_val T →
    is_val U →
    (* U might depend on x:T *)
    is_val e ->
    is_val (Lam x T f U e)
  .


Lemma norm_sound e: 
    normalized e -> normalized_pred e.
Proof.
  induction 1.
  all:unfold normalized_pred;intros [e' Hstep].
  all:inversion Hstep;subst.
  1-7: destruct K;simpl in *;inversion H;subst.
  1-7: now inversion H1.
  1: {
    destruct K;simpl in *;inversion H1;subst.
    - inversion H3.
    - unfold normalized_pred in IHnormalized1.
      contradict IHnormalized1.
      eexists.
      econstructor;eauto.
    - unfold normalized_pred in IHnormalized2.
      contradict IHnormalized2.
      eexists.
      econstructor;eauto.
  }
  1: {
    destruct K;simpl in *;inversion H3;subst.
    - inversion H5.
    - unfold normalized_pred in IHnormalized1.
      contradict IHnormalized1.
      eexists.
      econstructor;eauto.
    - unfold normalized_pred in IHnormalized2.
      contradict IHnormalized2.
      eexists.
      econstructor;eauto.
    - unfold normalized_pred in IHnormalized3.
      contradict IHnormalized3.
      eexists.
      econstructor;eauto.
    - unfold normalized_pred in IHnormalized4.
      contradict IHnormalized4.
      eexists.
      econstructor;eauto.
  }
  {
    destruct K; simpl in *;inversion H2;subst.
    - inversion H4;subst.
      contradict H1.
      do 5 eexists;eauto.
    - unfold normalized_pred in IHnormalized1.
      contradict IHnormalized1.
      eexists.
      econstructor;eauto.
    - unfold normalized_pred in IHnormalized2.
      contradict IHnormalized2.
      eexists.
      econstructor;eauto.
  }
Qed.


Lemma norm_sound2 e: 
    normalized_pred e -> normalized e.
Proof.
  induction e;intros H.
  1-7: constructor.
  - enough (normalized_pred e1 /\ normalized_pred e2).
    { constructor;[apply IHe1|apply IHe2];now destruct H0. }
    unfold normalized_pred in *. split.
    + contradict H;destruct H as [? []];subst.
      eexists. econstructor;eauto.
      instantiate (1:=FPi1 x K e2).
      reflexivity.
    + contradict H;destruct H as [? []];subst.
      eexists. econstructor;eauto.
      instantiate (1:=FPi2 x e1 K).
      reflexivity.
  - constructor;[apply IHe1|apply IHe2|apply IHe3|apply IHe4].
    all: unfold normalized_pred in *;intros [e' []];apply H;subst.
    all: eexists;econstructor;eauto.
    + now instantiate (1:=FLam1 x K e2 e3 e4).
    + now instantiate (1:=FLam2 x e1 K e3 e4).
    + now instantiate (1:=FLam3 x e1 e2 K e4).
    + now instantiate (1:=FLam4 x e1 e2 e3 K).
  - assert(normalized_pred e1 /\ normalized_pred e2) as [? ?].
    {
      split.
      all: unfold normalized_pred in *;intros [e' []];apply H;subst.
      all: eexists;econstructor;eauto.
      + now instantiate (1:=FApp1 K e2).
      + now instantiate (1:=FApp2 e1 K).
    }
    constructor;[apply IHe1|apply IHe2|];try eassumption.
    {
      apply IHe1 in H0.
      apply IHe2 in H1.
      unfold normalized_pred in H.
      contradict H.
      destruct H as (?&?&?&?&?&[]);subst.
      inversion H0;subst.
      eexists.
      econstructor;eauto.
      2: econstructor.
      2: reflexivity.
      1: {
        instantiate (6:=FHoleCtx).
        simpl. reflexivity.
      }
      all: try eassumption.
    }
Qed.


(*
our beta does not require normalization/evaluation per se (although every applicable expression will be normalized)
*)
(* also see https://coq.inria.fr/doc/v8.18/refman/language/core/conversion.html *)
Inductive base_step : expr -> expr -> Prop :=
(* 'real' steps (congruence steps later via contexts) *)
  | BetaS x T f U elam earg e' :
    e' = subst' x earg elam ->
    base_step (App (Lam x T f U elam) earg) e'
  .


(*
We go in every subexpression and under binder
*)
Inductive ectx :=
  | HoleCtx
  | LamCtxT (x:binder) (K: ectx) (f:expr) (U:expr) (e:expr)
  | LamCtxU (x:binder) (T: expr) (f:expr) (K:ectx) (e:expr)
  | LamCtx (x:binder) (T: expr) (f:expr) (U:expr) (K: ectx)
  | AppLCtx (K: ectx) (v2 : expr)
  | AppRCtx (e1 : expr) (K: ectx) 
  | PiCtxT (x:binder) (K: ectx) (U:expr)
  | PiCtxU (x:binder) (T:expr) (K: ectx)
  .  

(* Place an expression into the hole of a context *)
Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | LamCtxT x K f U eb => Lam x (fill K e) f U eb
  | LamCtxU x T f K eb => Lam x T f (fill K e) eb
  | LamCtx x T f U K => Lam x T f U (fill K e)
  | PiCtxT x K U => Pi x (fill K e) U
  | PiCtxU x T K => Pi x T (fill K e)
  | AppLCtx K v2 => App (fill K e) v2
  | AppRCtx e1 K => App e1 (fill K e)
  end.

(* Compose two evaluation contexts => place the second context into the hole of the first *)
Fixpoint comp_ectx (K1: ectx) (K2 : ectx) : ectx :=
  match K1 with
  | HoleCtx => K2
  | LamCtxT x K f U eb => LamCtxT x (comp_ectx K K2) f U eb
  | LamCtxU x T f K eb => LamCtxU x T f (comp_ectx K K2) eb
  | LamCtx x T f U K => LamCtx x T f U (comp_ectx K K2)
  | PiCtxT x K U => PiCtxT x (comp_ectx K K2) U
  | PiCtxU x T K => PiCtxU x T (comp_ectx K K2)
  | AppLCtx K v2 => AppLCtx (comp_ectx K K2) v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K2)
  end.


(** Contextual steps => lift reductions via contexts *)
Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    base_step e1' e2' → contextual_step e1 e2.

Definition reducible (e : expr) :=
  ∃ e', contextual_step e e'.


Definition empty_ectx := HoleCtx.

(** Basic properties about the language *)
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 → contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 → contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

Lemma values_dont_reduce e:
  is_val e → ¬ reducible e.
Proof.
  intros Hv Hred.
  destruct Hred.
  destruct H as [K e1 e2 -> -> Hred].
  induction K;simpl in Hv;inversion Hv;subst;try congruence.
  all: try (now inversion Hred).
  - inversion Hred. subst.
    now contradict H.
  - destruct K; simpl in *;inversion H0;subst.
    now contradict IHK.
  - (* Idx #n, Idx -> ... *)
    destruct K;simpl in *;inversion H1;subst.
    inversion Hred.
Qed.




 Lemma contextual_step_lambda x T f U e1 e2:
  contextual_step e1 e2 →
  contextual_step (Lam x T f U e1) (Lam x T f U e2).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (LamCtx x T f U HoleCtx)).
Qed.

Lemma contextual_step_lambda_domain x T1 T2 f U e:
  contextual_step T1 T2 →
  contextual_step (Lam x T1 f U e) (Lam x T2 f U e).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (LamCtxT x HoleCtx f U e)).
Qed.

Lemma contextual_step_lambda_codomain x T f U1 U2 e:
  contextual_step U1 U2 →
  contextual_step (Lam x T f U1 e) (Lam x T f U2 e).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (LamCtxU x T f HoleCtx e)).
Qed.

Lemma contextual_step_pi_domain x T U T':
  contextual_step T T' →
  contextual_step (Pi x T U) (Pi x T' U).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (PiCtxT x HoleCtx U)).
Qed.

Lemma contextual_step_pi_codomain x T U U':
  contextual_step U U' →
  contextual_step (Pi x T U) (Pi x T U').
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (PiCtxU x T HoleCtx)).
Qed.

Lemma contextual_step_app_l e1 e1' e2:
  contextual_step e1 e1' →
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (AppLCtx HoleCtx e2)).
Qed.

Lemma contextual_step_app_r e1 e2 e2':
  (* is_val e1 → *)
  contextual_step e2 e2' →
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

#[export]
Hint Resolve 
  contextual_step_lambda 
  contextual_step_lambda_domain
  contextual_step_lambda_codomain
  contextual_step_pi_domain
  contextual_step_pi_codomain
  contextual_step_app_l contextual_step_app_r : core.



Lemma norm_inversion_Bot e:
  normalize_step Bot e → e = Bot.
Proof.
  intros Hnorm.
  inversion Hnorm;subst;auto.
Qed.



(*
full_contextual_step is defined over contexts
we extend it to rtc
*)
Lemma rtc_full_contextual_context e e' e1 e1' K:
  rtc full_contextual_step e1 e1' →
  e = full_fill K e1 →
  e' = full_fill K e1' →
  rtc full_contextual_step e e'.
Proof.
  induction 1 in e,e' |- *;intros Hfill Hfill2.
  - subst. constructor.
  - subst. 
    destruct H;subst.
    econstructor.
    + eapply Fectx_step with (K:= comp_full_ectx K K0);eauto.
      now rewrite full_fill_comp.
    + rewrite full_fill_comp.
      now apply IHrtc.
Qed.

Lemma rtc_rtc {A:Type} {R:relation A} e e' e'':
  rtc R e e' →
  rtc R e' e'' →
  rtc R e e''.
Proof.
  induction 1;auto.
  intros Hrtc.
  econstructor;[|apply IHrtc];eauto.
Qed.





Notation "e →ᵦ e'" := (contextual_step e e') (at level 50).
Notation "e →ₙ e'" := (normal_eval e e') (at level 50).
Notation "e →ᵦ* e'" := (rtc (contextual_step) e e') (at level 50).

Definition beta_normal_step e e' :=
  exists e_aux, e →ᵦ e_aux /\ e_aux →ₙ e'.

Notation "e →ᵦₙ e'" := (beta_normal_step e e') (at level 50).
Notation "e →ᵦₙ* e'" := (rtc beta_normal_step e e') (at level 50).

