From stdpp Require Export binders strings.
From iris.prelude Require Import options.
From thorin.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Inductive expr :=
  | Star
  | Box
  | Bot
  | Nat
  | Idx 
  | LitNat (n : nat)
  | LitIdx (n : nat) (i:Fin.t n)
  | Var (x : string)
  (* let is already normalized *)
  (* axiom is already handled *)
  | Pi (x : binder) (T U : expr)
  (* lam has a filter expression *)
  | Lam (x : binder) (T : expr) (f : expr) (U: expr) (e: expr)
  | App (e1 e2 : expr)
  | Sigma (args: list (binder * expr))
  | Tuple (es : list expr)
  | Array (x: binder) (en: expr) (T: expr)
  | Pack (x: binder) (en: expr) (e: expr)
  | Extract (e: expr) (ei: expr)
.

Bind Scope expr_scope with expr.

(*
  We argue at some points over lists.
  We could use ∀x∈xs. P x
  However, we want a stronger statement:
  - Computational (not Prop)
  - List structure linked to xs
  - Able to use induction/destructuring on the strucutre

  https://ps.uni-saarland.de/~ullrich/bachelor.php
  https://github.com/NeuralCoder3/parametricity-note

  We use the unary ∀ parametricity relation
  For lists, this is Forall.
*)


(* 
  Semantics uses an additional val type with of_val, to_val and conversions between them.
  They need it to simplify the definition of computational steps (e.g. un_op_eval/bin_op_eval). (but not significantly)

  To me, a inductive predicate is_val seems to be shorter and simpler.
  All our proofs only argue about is_val.
*)

Inductive is_val : expr → Prop :=
  | StarV : is_val Star
  | BoxV : is_val Box
  | BotV : is_val Bot
  | NatV : is_val Nat
  | IdxV : is_val Idx
  (* TODO: is (Idx n) a value? if not what does it reduce to *)
  | IdxAppV n : is_val (App Idx (LitNat n))
  | LitNatV n : is_val (LitNat n)
  | LitIdxV n i : is_val (LitIdx n i)
  | PiV x T U : 
    is_val T →
    is_val (Pi x T U)
  | LamV x T f U e : 
    is_val T →
    (* U might depend on x:T *)
    is_val (Lam x T f U e)
  (* compound values *)
  (* sigma would not be strictly positive
    => either two lists or use the val type

    however, sigma is like lambda (functions depending on previous values)
    => only the first one should be a val
  *)
  | SigmaEmptyV: is_val (Sigma [])
  (* we do not need to test the rest => (implicitely) depends on first one *)
  | SigmaConsV x T args : is_val T → is_val (Sigma ((x, T) :: args))
  | TupleV es : Forall is_val es → is_val (Tuple es)
  | ArrayV x en T : 
    is_val en →
    is_val (Array x en T)
  | PackV x en e :
    is_val en →
    is_val (Pack x en e)
  .

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  let recurse_under y expr := if decide (y = BNamed x) then expr else subst x es expr in
  match e with
  | Star | Box | Bot | Nat | Idx | LitNat _ | LitIdx _ _  => e
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
  (* map over nested induction 
  => use inner fixpoint 
  mutual recursion is not recognized (https://coq.discourse.group/t/mutual-recursion-for-nested-inductive-types/729/3)
  Equations would be possible but not necessarily easier
   *)
  | Tuple expression =>
    Tuple (map (subst x es) expression)
  (* for Sigma, we only continue subst in args if not already encountered var *)
  | Sigma xs =>
    Sigma ((fix fold_subst (xs : list (binder * expr)) : list (binder * expr) :=
      match xs with
      | [] => []
      | (y, T) :: xs => 
        (* stop at [x:..., ...] => later x are regarding the parameter*)
        (y, subst x es T) :: (if decide (y = BNamed x) then xs else fold_subst xs)
      end) xs)
  | Array y en T => Array y (subst x es en) (recurse_under y T)
  | Pack y en e => Pack y (subst x es en) (recurse_under y e)
  | Extract e ei => Extract (subst x es e) (subst x es ei)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

(* Notation "e . [ x / e2 ]" := (subst x e2 e) (at level 20). *)
(* Notation "e '.' '[' e2 '/' x ']'" := (subst' x e2 e) (at level 20).
Check (Lam (BNamed "x") Nat (Var "x") Nat (Var "x")).[LitNat 3 / "x"]. *)

(* https://coq.inria.fr/doc/v8.18/refman/language/core/conversion.html *)
Inductive base_step : expr -> expr -> Prop :=
(* 'real' steps (congruence steps later) *)
  | BetaS x T f U elam earg e' :
  (* TODO: necessary to completely eval T? should probably be *)
    is_val T ->
    is_val earg ->
    e' = subst' x earg elam ->
    base_step (App (Lam x T f U elam) earg) e'
  | IotaTupleS es n (i:Fin.t n) e:
    (* extract from a tuple if all value *)
    (* needs canonical form lemma for Idx n *)
    (*
    for nth, we need a proof about the size
    alternatively, a vector would work but we would have the size everywhere
    *)
    Forall is_val es ->
    length es = n ->
    nth_error es (` (Fin.to_nat i)) = Some e ->
    base_step (Extract (Tuple es) (LitIdx n i)) e
  (* extract of pack *)
  | IotaPackS x e n ei e':
    is_val ei -> (* implies ei = LitIdx n i (via canonical values?) *)
    e' = subst' x ei e ->
    base_step (Extract (Pack x (LitNat n) e) ei) e'
  .



Lemma fin_inc n (i:Fin.t n): (` (Fin.to_nat (Fin.FS i))) = S (` (Fin.to_nat i)).
Proof.
  induction i; simpl.
  - reflexivity.
  - admit.
Admitted.

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

(* evaluation contexts for congruence reduction *)
(* a hole/context is an evaluation point *)
(*
  one difference is that semantics uses val to restrict the contexts
  to an evaluation from right to left
  We use additional is_val to restrict the contexts

  only relevant for two sided reductions in app, extract, and tuple

  Note: we are a bit lazier => do not evaluate under binders
*)
Inductive ectx :=
  | HoleCtx
  (* only context in T as U might depend on x:T *)
  | PiCtx (x:binder) (K: ectx) (U:expr) 
  (* the filter depends on the argument *)
  | LamCtx (x:binder) (K: ectx) (f:expr) (U:expr) (e:expr)
  | AppLCtx (K: ectx) (v2 : expr)
  | AppRCtx (e1 : expr) (K: ectx) (H: is_val e1)
  (* only first argument in sigma *)
  | SigmaCtx (x:binder) (K: ectx) (args: list (binder * expr))
  | TupleCtx (es1:list expr) (K: ectx) (es2: list expr) (H: Forall is_val es1)
  (* only en is up to be a context *)
  | ArrayCtx (x:binder) (K: ectx) (T:expr)
  | PackCtx (x:binder) (K: ectx) (e:expr)
  | ExtractLCtx (K: ectx) (ei:expr)
  | ExtractRCtx (e:expr) (K: ectx) (H: is_val e)
  .  

(* Place an expression into the hole of a context *)
Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | PiCtx x K U => Pi x (fill K e) U
  | LamCtx x K f U eb => Lam x (fill K e) f U eb
  | AppLCtx K v2 => App (fill K e) v2
  | AppRCtx e1 K _ => App e1 (fill K e)
  | SigmaCtx x K args => Sigma ((x, fill K e) :: args)
  | TupleCtx es1 K es2 _ => Tuple (es1 ++ fill K e :: es2)
  | ArrayCtx x K T => Array x (fill K e) T
  | PackCtx x K eb => Pack x (fill K e) eb
  | ExtractLCtx K ei => Extract (fill K e) ei
  | ExtractRCtx eb K _ => Extract eb (fill K e)
  end.

(* Compose two evaluation contexts => place the second context into the hole of the first *)
Fixpoint comp_ectx (K1: ectx) (K2 : ectx) : ectx :=
  match K1 with
  | HoleCtx => K2
  | PiCtx x K U => PiCtx x (comp_ectx K K2) U
  | LamCtx x K f U e => LamCtx x (comp_ectx K K2) f U e
  | AppLCtx K v2 => AppLCtx (comp_ectx K K2) v2
  | AppRCtx e1 K H => AppRCtx e1 (comp_ectx K K2) H
  | SigmaCtx x K args => SigmaCtx x (comp_ectx K K2) args
  | TupleCtx es1 K es2 H => TupleCtx es1 (comp_ectx K K2) es2 H
  | ArrayCtx x K T => ArrayCtx x (comp_ectx K K2) T
  | PackCtx x K e => PackCtx x (comp_ectx K K2) e
  | ExtractLCtx K ei => ExtractLCtx (comp_ectx K K2) ei
  | ExtractRCtx e K H => ExtractRCtx e (comp_ectx K K2) H
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

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Star | Box | Bot | Nat | Idx | LitNat _ | LitIdx _ _ => true
  | Var x => bool_decide (x ∈ X)
  | Pi x T U => is_closed X T && is_closed (x :b: X) U
  | Lam x T f U e => is_closed X T && is_closed (x :b: X) f && is_closed (x :b: X) U && is_closed (x :b: X) e
  | App e1 e2 => is_closed X e1 && is_closed X e2
  (* sigma closed under previous *)
  | Sigma args => (fix is_closed_sigma (X : list string) (args : list (binder * expr)) : bool :=
    match args with
    | [] => true
    | (x, T) :: args => is_closed X T && is_closed_sigma (x :b: X) args
    end) X args
  | Tuple es => forallb (is_closed X) es
  | Array x en T => is_closed X en && is_closed (x :b: X) T
  | Pack x en e => is_closed X en && is_closed (x :b: X) e
  | Extract e ei => is_closed X e && is_closed X ei
  end.

(* TODO: where do we need those lemmas?
  TODO: There are better ways to handle (or not) closedness
*)

(** [closed] states closedness as a Coq proposition, through the [Is_true] transformer. *)
Definition closed (X : list string) (e : expr) : Prop := Is_true (is_closed X e).
#[export] Instance closed_proof_irrel X e : ProofIrrel (closed X e).
Proof. unfold closed. apply _. Qed.
#[export] Instance closed_dec X e : Decision (closed X e).
Proof. unfold closed. apply _. Defined.

(** closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. 
  (* revert X Y; induction e; try naive_solver (eauto; set_solver).  *)
  (* TODO: the list cases (Sigma, Tuple) => need neested induction *)
  all: admit.
Admitted.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?.
  induction e in X |-*; simpl; intros ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
  (* TODO: check *)
  all: admit.
Admitted.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(** Substitution lemmas *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  induction e in X |-*; simpl; rewrite ?bool_decide_spec, ?andb_True; intros ??;
    repeat case_decide; simplify_eq; simpl; f_equal; intuition eauto with set_solver.
  (* TODO: check *)
  all: admit.
Admitted.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.
Lemma subst'_is_closed_nil e x es : is_closed [] e → subst' x es e = e.
Proof. intros. destruct x as [ | x]. { done. } by apply subst_is_closed_nil. Qed.















(* we derive a few lemmas about contextual steps *)
(*
we need these lemmas for progress
=> if inner expression not value, we can lift a contextual step over a context
however, the context is an indirection over a simplification requiring a lemma to ease the automation burdon
*)

Lemma contextual_step_pi x T U T':
  contextual_step T T' →
  contextual_step (Pi x T U) (Pi x T' U).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PiCtx x HoleCtx U)).
Qed.

Lemma contextual_step_lam x ef U e T T':
  contextual_step T T' →
  contextual_step (Lam x T ef U e) (Lam x T' ef U e).
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (LamCtx x HoleCtx ef U e)).
Qed.

Lemma contextual_step_app_l e1 e1' e2:
  contextual_step e1 e1' →
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (AppLCtx HoleCtx e2)).
Qed.

Lemma contextual_step_app_r e1 e2 e2':
  is_val e1 →
  contextual_step e2 e2' →
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros H Hcontextual.
  by apply (fill_contextual_step (AppRCtx e1 HoleCtx H)).
Qed.

(* TODO: complete other lemmata about contextual steps *)

Lemma contextual_step_extract_l e e' ei:
  contextual_step e e' →
  contextual_step (Extract e ei) (Extract e' ei).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (ExtractLCtx HoleCtx ei)).
Qed.

Lemma contextual_step_extract_r e ei ei':
  is_val e →
  contextual_step ei ei' →
  contextual_step (Extract e ei) (Extract e ei').
Proof.
  intros H Hcontextual.
  by apply (fill_contextual_step (ExtractRCtx e HoleCtx H)).
Qed.

#[export]
Hint Resolve
  contextual_step_lam
  contextual_step_app_l
  contextual_step_app_r
  (* ... *)
  contextual_step_extract_l
  contextual_step_extract_r
  : core.



