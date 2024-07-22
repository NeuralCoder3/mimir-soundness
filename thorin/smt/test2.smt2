(set-logic AUFNIRA)

(declare-fun even (Int) Bool)
(assert (forall ((x Int)) (= (even x) (exists ((y Int)) (= x (* 2 y))))))

; (assert (even 2))
; (assert (even 3))
(assert (even 4))
(assert true)
; Solve
(check-sat)
(get-model)
