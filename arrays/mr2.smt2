(set-logic ALL)
(assert (exists ((a (Array Int Int)) (b (Array Int Int))) (distinct a b)))
(check-sat)
