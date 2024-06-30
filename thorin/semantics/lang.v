From stdpp Require Export binders strings.
From iris.prelude Require Import options.
From thorin.lib Require Export maps.

Declare Scope expr_scope.
Declare Scope val_scope.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(*

open conceptual TODO:
- some missing assumptions/mistakes in the pdf
- is a lam with normalized type also a value or only if the type is evaluated (a value)
- recheck: normalization is no subset of evaluation (normalization goes under binders)
  - does normalization go under binder?
- TODO: how to formalize normalization
- does order (left-to-right, bottom-up) matter for normalization
- ----
- the proof are technically hard:
  - mutual induction with assignability
  - nested induction with the lists
  - normalization in between on type level
- name clashes for substitutivity
- is a variable a value? if not, it is not progressing
- typing does normalization => base step preservation needs to argue that type already normalized or we need to normalize again
- preservation of the form "if typed, then normalized is value or steps"?



Normalization:
- pre-requirement for reduction
- not performed in reduction currently (we always argue about one reduction step)
  - we can assert normalize before and conceptually normalize afterward
- currently, 


λ (x:T) : U @ef, eb
we do not reduce under binders => only redex is T
we use λ in app if T is normalized
=> TODO: is_val should be true if T is normalized
hence, we conceptually (and practically) only reduce until T is normalized
but by construction, T is normalized
=> TODO: a few consequences
- on type level, normalization is our value relation
- is_val should rely on normalized
- relation to beta
  - (without norm as pre-op, norm should not go under binders)
  - 'beta reduce until norm' does not really hold (and if so only if not under binder)
- TODO: there should not be any type reduxes (except maybe toplevel?)
  - no redex in the type of a lambda
  - can Pi have a redex => should have, right?





A short outline of the document.
Each part has its own comments with relevant explanations.

Outline lang.v:
- expr -- Expression type of thorin
- is_val
- subst
- normalize_step -- a single toplevel normalization step according to ▹
- full_ectx -- Full contexts going through binders
- full_contextual_step -- doing a step under a context
- normal_eval -- predicate to relate an expression to its normal(ized) form
- base_step -- a single toplevel reduction step
- ectx -- evaluation contexts for reductino
- contextual_step -- step under a context
- contextual_step lemmas -- if subexpression steps, whole expression steps

Outline types_sol.v:
- syn_typed -- typing derivation, assignability relation
- typed_weakening -- we can extend the context
- typed_substitutivity -- subst in context, expression, type
- canonical value lemma -- if value has some type, it has some shape
- typed_progress -- typed expressions can reduce or are a value (TODO: needs normalization)
- typed_preservation_base_step -- a toplevel reduction preserves types
- typed_preservation -- preservation over multiple steps

*)




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
  (* 
    sigma is like lambda (functions depending on previous values)
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



Require Import Coq.Program.Equality.

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

(* TODO: require normalized subexpressions? (would be needed for in-to-out-order) *)
Inductive normalize_step : expr -> expr -> Prop :=
  (* no let *)
  | normalize_extract_one e:
    (* TODO: need normalized of e? *)
    normalize_step (Extract e (LitIdx 1 Fin.F1)) e
  | normalize_tuple_one e:
    normalize_step (Tuple [e]) e
  | normalize_sigma_one xT:
    normalize_step (Sigma [xT]) (Sigma [xT])
  | normalize_tuple_beta xs n i e:
    length xs = n ->
    nth_error xs (` (Fin.to_nat i)) = Some e ->
    (* TODO: maybe we could model this using vectors *)
    normalize_step (Extract (Tuple xs) (LitIdx n i)) e
  | normalize_pack_beta en e ei:
    normalize_step (Extract (Pack BAnon en e) ei) e
  | normalize_tuple_eta e n:
    (* TODO: n>1 missing from paper *)
    n > 1 ->
    normalize_step (Tuple (map (fun i => Extract e (LitIdx n i)) (ltac: (destruct (fin_list n) as [xs _];exact xs)))) e
  | normalize_pack_tuple n e:
    (* replicate is the same as repeat *)
    n > 1 ->
    normalize_step (Tuple (replicate n e)) (Pack (BAnon) (LitNat n) e)
  | normalize_array_sigma n T:
    n > 1 ->
    normalize_step (Sigma (replicate n (BAnon, T))) (Array (BAnon) (LitNat n) T)
  | normalize_beta x T ef U eb ea:
    (* TODO: ef[ea/x] beta equiv true *)
    ef = ETrue ->
    normalize_step (App (Lam x T ef U eb) ea) (subst' x ea eb)
  | normalize_tuple_pack x n e:
    normalize_step (Pack (BNamed x) (LitNat n) e) (Tuple (instantiate x n e))
  | normalize_sigma_array x n T:
    normalize_step (Array (BNamed x) (LitNat n) T) (Sigma (map (fun x => (BAnon, x)) (instantiate x n T)))
.

(* TODO: do we need to require left-to-right or in-to-out order? *)
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
  | FSigma (xs1: list (binder * expr)) (x:binder) (K: full_ectx) (xs2: list (binder * expr))
  | FTuple (es1:list expr) (K: full_ectx) (es2: list expr)
  | FArray1 (x:binder) (en: full_ectx) (T:expr)
  | FArray2 (x:binder) (en: expr) (T: full_ectx)
  | FPack1 (x:binder) (en: full_ectx) (e:expr)
  | FPack2 (x:binder) (en: expr) (e: full_ectx)
  | FExtract1 (K: full_ectx) (ei:expr)
  | FExtract2 (e:expr) (K: full_ectx)
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
  | FSigma xs1 x K xs2 => Sigma (xs1 ++ (x,full_fill K e) :: xs2)
  | FTuple es1 K es2 => Tuple (es1 ++ full_fill K e :: es2)
  | FArray1 x K T => Array x (full_fill K e) T
  | FArray2 x en K => Array x en (full_fill K e)
  | FPack1 x K eb => Pack x (full_fill K e) eb
  | FPack2 x en K => Pack x en (full_fill K e)
  | FExtract1 K ei => Extract (full_fill K e) ei
  | FExtract2 eb K => Extract eb (full_fill K e)
  end.

Inductive full_contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Fectx_step K e1' e2' :
    e1 = full_fill K e1' → e2 = full_fill K e2' →
    normalize_step e1' e2' → full_contextual_step e1 e2.

Definition normalizable (e : expr) :=
  ∃ e', full_contextual_step e e'.

Definition normalized_pred (e : expr) :=
  ~ ∃ e', full_contextual_step e e'.

  (* maybe as inductive? *)
  (* perform all possible normalization redexes *)
Definition normal_eval e e' :=
  rtc full_contextual_step e e' ∧ normalized_pred e'.

(*
  a bit more constructive version
  => subexpressions and contradict normalization step in negative assumptions
*)
Inductive normalized : expr -> Prop :=
  (* atomic values *)
  (* conceptually, every value is normalized (not quite -- normalization goes under binders) *)
  (* but for distinction, differences and adaptation, we should keep normalization without is_val *)
  | norm_Star: normalized Star
  | norm_Box: normalized Box
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
    (* TODO: not = ETrue but beta equiv to True *)
    ~(exists x T f U e, e1 = Lam x T f U e /\ f = ETrue) ->
    normalized (App e1 e2)

  (*
    Sigma
    - subexpressions normalized
    - not unary
    - no unnamed array sigma [T, ..., T]
  *)
  | norm_Sigma xs:
    (* without map separately, it would be a not strictly positive occurence of normalized *)
    Forall normalized (map (fun '(x,T) => T) xs) ->
    xs = [] \/ length xs > 1 ->
    ~ (length xs > 1 /\ exists T, Forall (fun b => b = (BAnon, T)) xs) ->
    normalized (Sigma xs)

  (* Tuple
    - subexpressions normalized 
    - not unary 
    - not eta tuple (e#i, i in 0..n-1) 
    - not pack tuple (e, ..., e) 
  *)
  | norm_Tuple es:
    Forall normalized es ->
    es = [] \/ length es > 1 ->
    ~ (length es > 1 /\ 
      exists e, 
        Forall2 (fun ei idx => ei = Extract e (LitIdx (length es) idx))
          es (let (xs,_) := fin_list (length es) in xs)
    ) ->
    ~ (length es > 1 /\ exists e, es = replicate (length es) e) ->
    normalized (Tuple es)

  (*
    Array
    - subexpressions normalized
    - no named & nat size
  *)
  | norm_Array x en T:
    normalized en -> normalized T -> 
    ~ (exists s n, x = BNamed s /\ en = LitNat n) ->
    normalized (Array x en T)

  (*
    Pack
    - subexpressions normalized
    - no named & nat size
  *)
  | norm_Pack x en e:
    normalized en -> normalized e -> 
    ~ (exists s n, x = BNamed s /\ en = LitNat n) ->
    normalized (Pack x en e)

  (*
    Extract
    - subexpressions normalized
    - no extract 0_1
    - no extract of tuple with idx
    - no extract of unnamed pack
  *)
  | norm_Extract e ei:
    normalized e -> normalized ei -> 
    ~ (ei = LitIdx 1 Fin.F1) ->
    ~ (exists es idx, e = Tuple es /\ ei = LitIdx (length es) idx) ->
    ~ (exists en eb, e = Pack BAnon en eb) ->
    normalized (Extract e ei)
  .

Lemma normalized_sound e:
  (* normalized_pred := ~ normalizable *)
  normalized e -> ~ normalizable e.
Proof.
  induction 1;intros [e' Hnorm].
  1-8: (
    destruct Hnorm;subst;
    destruct K;simpl in *;inversion H;subst;
    inversion H1
  ).
  (* 
  - (* Star *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H;subst.
    inversion H1.
  *)
  (* - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit. *)
  (*
    we look at the normalization step and context
    => is the context toplevel or a subexpression
    for toplevel: which normalization step
      each normalization step contradicted by assumption
    each subexpression contradiction
  *)
  - (* Pi *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H1;subst.
    + inversion H3. (* Pi does not make a norm step *)
    + contradict IHnormalized1.
      eexists.
      econstructor;eauto.
    + contradict IHnormalized2.
      eexists.
      econstructor;eauto.
  - (* Lam -- similar to Pi *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H3;subst.
    + inversion H5.
    + contradict IHnormalized1;eexists;econstructor;eauto.
    + contradict IHnormalized2;eexists;econstructor;eauto.
    + contradict IHnormalized3;eexists;econstructor;eauto.
    + contradict IHnormalized4;eexists;econstructor;eauto.
  - (* App *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H2;subst.
    + inversion H4;subst.
      contradict H1.
      do 5 eexists;eauto.
    + contradict IHnormalized1.
      eexists.
      econstructor;eauto.
    + contradict IHnormalized2.
      eexists.
      econstructor;eauto.
  - (* Sigma *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H2;subst.
    + inversion H4;subst.
      * (* unary Sigma *)
        simpl in H0.
        destruct H0;try congruence.
        lia.
      * (* replicate *)
        contradict H1.
        split.
        -- now rewrite replicate_length.
        -- exists T. admit. (* easy *)
    + admit. (* needs nested induction *)
  - (* Tuple *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H3;subst.
    + inversion H5;subst.
      * destruct H0;eauto. inversion H0.
      * contradict H1.
        admit.
      * contradict H2. split.
        -- rewrite replicate_length. easy.
        -- rewrite replicate_length. eauto.
    + admit. (* needs nested induction *)
  - (* Array *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H2;subst.
    + inversion H4;subst.
      contradict H1.
      eauto.
    + contradict IHnormalized1;eexists;econstructor;eauto.
    + contradict IHnormalized2;eexists;econstructor;eauto.
  - (* Pack *)
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H2;subst.
    + inversion H4;subst.
      contradict H1. eauto.
    + contradict IHnormalized1;eexists;econstructor;eauto.
    + contradict IHnormalized2;eexists;econstructor;eauto.
  - (* Extract *) 
    destruct Hnorm;subst.
    destruct K;simpl in *;inversion H4;subst.
    + inversion H6;subst.
      * now contradict H1.
      * contradict H2. eauto.
      * contradict H3. eauto.
    + contradict IHnormalized1;eexists;econstructor;eauto.
    + contradict IHnormalized2;eexists;econstructor;eauto.
Admitted.












(*
Importantly, we do not evaluate on type level, we just normalize
normalization is a subset/prestep of full evaluation

on expression level, we want full eager (cbv) eval => values

TODO: where to apply normalization?
As extra reduction step (+normalized requirement?)? As separate step in between?
*)


(* https://coq.inria.fr/doc/v8.18/refman/language/core/conversion.html *)
Inductive base_step : expr -> expr -> Prop :=
(* 'real' steps (congruence steps later) *)
  | BetaS x T f U elam earg e' :
    normalized T ->
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
    (*
    TODO: need normalization here?
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




(* evaluation contexts for congruence reduction *)
(* a hole/context is an evaluation point *)
(*
  one difference is that semantics uses val to restrict the contexts
  to an evaluation from right to left
  We use additional is_val to restrict the contexts (should be correct here)

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

(* TODO: we want is_val <-> ~ reducibile *)
Lemma values_dont_reduce e:
  is_val e → ¬ reducible e.
Proof.
  intros Hv Hred.
  destruct Hred.
  destruct H as [K e1 e2 -> -> Hred].
  induction K;simpl in Hv;inversion Hv;subst;try congruence.
  all: try (now inversion Hred).
  - (* Idx #n, Idx -> ... *)
    destruct K;simpl in *;inversion H0;subst.
    inversion Hred.
  - (* Idx #n, #n -> ... *)
    destruct K;simpl in H2;inversion H2;subst.
    inversion Hred.
  - apply Forall_app in H1 as [H1 H2].
    inversion H2;subst.
    congruence.
Qed.

(*
lemma is_val -> normalized
equivalent: normalizable -> reducable

TODO: does not hold!
we normalize under binders but do not reduce under binders
*)
(* Lemma normalized_values e:
  is_val e → normalized e.
Proof.
  (* could go the step over 
    val -> ~red
    normalizable -> reduce
   *)
   intros Hval [e' Hnormstep].
   inversion Hnormstep;subst.
   induction K;simpl in *.
   - inversion H1;subst;admit.
   - inversion Hval;subst.
     apply IHK;eauto.
     eapply Fectx_step with (K:=K);eauto.
   - 

   dependent induction Hval;simpl in *.
   - 
   all: inversion H1;subst.
   - 

Abort. *)

(* TODO: possibly multiple steps 
  e.g. <_:n;e>#ei ->n e
  <_:n;e>#ei 
    -> <_:vn;e>#ei 
    -> <_:vn;e>#vi 
    -> e

  => use progress lemma

  e#0_1 -> e
  use canonical values => tuple/pack
*)
Lemma norm_red e e':
    normalize_step e e' → base_step e e'.
Proof.
  intros Hnorm.
  inversion Hnorm;subst.
Abort.

(* TODO: not necessarily: the redex might be under a binder *)
(* Lemma normalizable_reducible e:
  normalizable e → reducible e.
Proof.
  intros [e' Hnorm].
  inversion Hnorm;subst.
  eexists.
  induction H1.
Abort. *)





(* Fixpoint is_closed (X : list string) (e : expr) : bool :=
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
Proof. intros. destruct x as [ | x]. { done. } by apply subst_is_closed_nil. Qed. *)















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

Lemma contextual_step_sigma x T T' xs:
  contextual_step T T' →
  contextual_step (Sigma ((x, T) :: xs)) (Sigma ((x, T') :: xs)).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (SigmaCtx x HoleCtx xs)).
Qed.

Lemma contextual_step_tuple es es' e e':
  Forall is_val es →
  contextual_step e e' →
  contextual_step (Tuple (es ++ e :: es')) (Tuple (es ++ e' :: es')).
Proof.
  intros Hval Hcontextual.
  by apply (fill_contextual_step (TupleCtx es HoleCtx es' Hval)).
Qed.

Lemma contextual_step_array x en en' T:
  contextual_step en en' →
  contextual_step (Array x en T) (Array x en' T).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (ArrayCtx x HoleCtx T)).
Qed.

Lemma contextual_step_pack x en en' e:
  contextual_step en en' →
  contextual_step (Pack x en e) (Pack x en' e).
Proof.
  intros Hcontextual.
  by apply (fill_contextual_step (PackCtx x HoleCtx e)).
Qed.

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
  contextual_step_pi
  contextual_step_lam
  contextual_step_app_l
  contextual_step_app_r
  contextual_step_sigma
  contextual_step_tuple
  contextual_step_array
  contextual_step_pack
  contextual_step_extract_l
  contextual_step_extract_r
  : core.



