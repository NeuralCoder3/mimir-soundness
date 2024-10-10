From thorin Require Export lang.
Set Default Proof Using "Type".

Coercion LitNat : nat >-> expr.
Coercion App : expr >-> Funclass.
Coercion Var : string >-> expr.

Notation "# l" := (LitNat l) (at level 8, format "# l") : expr_scope.
Notation "λ: ( x : T ) @ f : U , e" := (Lam x%binder T%E f%E U%E e%E)
  (at level 200,
   format "'[' 'λ:'  ( x  :  T )  @ f  :  U ,  '/  ' e ']'") : expr_scope.
