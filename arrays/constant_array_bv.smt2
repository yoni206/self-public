(set-logic ALL)

(define-sort BV () (_ BitVec 4))
(declare-const x BV)
(define-const zero BV (bvand x (bvnot x)))

(define-fun is_const_arr_0 ((a (Array BV BV))) Bool (forall ((i BV)) (= (select a i) zero)))

(assert (not (exists ((a (Array BV BV))) (is_const_arr_0 a))))

(check-sat)
