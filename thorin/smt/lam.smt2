(set-logic ALL)
; (set-logic AUFNIRA)
; (set-logic QF_LIA)

; smt2 definition of lambda calculus type
(declare-datatypes ((Typ 0)) (((Unit) (Arrow (arg Typ) (res Typ)))))
; now expressions
(declare-datatypes ((Exp 0)) (((Var (index Int)) (Abs (body Exp)) (App (fun Exp) (arg Exp)) (One))))

; (assert true)
; (declare-fun typed (Exp Typ) Bool)
; with environment
(declare-fun typed ((Array Int Typ) Exp Typ) Bool)

; x : A |- x : A
(assert (forall ((env (Array Int Typ)) (i Int) (A Typ))
  (=> 
    (= A (select env i))
    (typed env (Var i) A)
  )
))

; |- One : Unit
(assert (forall ((env (Array Int Typ)))
  (typed env One (Unit))
))
    
(declare-const e Exp)
; (assert (not (exists ((env (Array Int Typ)) (A Typ)) (typed env e A))))
(assert (forall ((env (Array Int Typ)) (A Typ)) (not (typed env e A))))

(check-sat)
(get-model)