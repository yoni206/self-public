(set-logic ALL)
(declare-datatype Sort ((unary  (param Sort)) (nullary)))
(declare-fun f1 (Sort) Sort)
(declare-fun f2 (Sort) Sort)
(define-fun formula () Bool (forall ((p Sort) (x Sort)) (=> (= x (unary p)) (and (= (f1 p) nullary) (= x (unary (f2 p)))))))

(assert formula)
(check-sat)
