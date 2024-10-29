(set-logic ALL)
(declare-datatype List ((cons (hd Int) (tl List)) (nil)))
(define-fun-rec length ((ls List)) Int
   (ite ((_ is nil) ls) 0 (+ 1 (length (tl ls)))))
(declare-const ls List)
(assert (< (length ls) 0))
(check-sat)
