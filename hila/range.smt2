(set-option :sygus-verify-inst-max-rounds -1)
(set-option :sygus-grammar-cons any-const)
(set-option :sygus-abort-size 4)
(set-option :incremental false)

(set-logic ALL)

(declare-fun lower () Int)
(declare-fun upper () Int)


(define-fun P ( ) Bool true)
(define-fun S ((x Int) (y Int) ) Bool (and (<= (- 100) x) (<= x y) (<= y 100)))
(define-fun b ((x Int) (y Int) ) Bool (and (<= lower x) (<= x upper)))

(assert (forall ((x Int) (y Int)) (=> P  (=> (S x y) (b x y)))))
(assert (forall ((x Int) (y Int)) (=> P  (=>  (b x y) (exists ((yy Int)) (S x yy))))))
(check-sat)
