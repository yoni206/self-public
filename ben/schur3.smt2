(set-logic ALL)

; In Ramsey theory, Schur's theorem states that for any partition of the
; positive integers into a finite number of parts, one of the parts contains
; three integers x, y, z with x+z

(declare-fun c (Int) Bool)
(declare-fun m () Int)



; (assert (>= m 1))
(assert (= m 9))
(assert (forall ( (x Int) (y Int)) (=> (and (> x 0) (> y 0) (< x y)  (<= (+ x y) m)) (not (and (= (c x) (c y)) (= (c x) (c (+ x y))  ))))))

(check-sat)
