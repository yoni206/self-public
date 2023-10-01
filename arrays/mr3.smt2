(set-logic ALL)
(assert (not (exists ((a (Array Int Int)) (b (Array Int Int))) (distinct a b))))
(check-sat)
