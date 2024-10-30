(set-logic ALL)
(declare-datatypes ((List 0)) (((cons (hd Int) (tl List)) (nil))))
(declare-fun length (List) Int)
(assert (forall ((ls List)) (= (length ls) (ite (= nil ls) 0 (+ 1 (length (tl ls)))))))
(assert (exists ((ls List)) (not (>= (length ls) 0))))

(check-sat)
