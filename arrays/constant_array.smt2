(set-logic ALL)

(define-fun is_const_arr_0 ((a (Array Int Int))) Bool (forall ((i Int)) (= (select a i) 0)))

(assert (not (exists ((a (Array Int Int))) (is_const_arr_0 a))))

(check-sat)
