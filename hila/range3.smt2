(set-logic ALL)

(declare-fun lower () Int)
(declare-fun upper () Int)

(declare-fun a1 () Int)
(declare-fun a2 () Int)

(define-fun lower_bound ((x Int)) Int (+ (* a1 x) lower))
(define-fun upper_bound ((x Int)) Int (+ (* a2 x) upper))


(define-fun P ( ) Bool true)
(define-fun S ((x Int) (y Int) ) Bool (and (<= (- 100) x) (<= x y) (<= y 100)))
(define-fun b ((x Int) (y Int) ) Bool (and (<= (lower_bound x) x) (<= x (upper_bound x))))

(assert (forall ((x Int) (y Int)) (=> P  (=> (S x y) (b x y)))))
(assert (forall ((x Int) (y Int)) (=> P  (=>  (b x y) (exists ((yy Int)) (S x yy))))))
(check-sat)
