(set-logic ALL)

; Schur 2: same as above but the partition is to 2 sets.
; For every coloring c there are x,y such that x,y,x+y 
; c(x)=c(y)=c(x+y)

(declare-fun c (Int) Bool)
(declare-fun m () Int)



; (assert (>= m 1))
(assert (= m 9))
(assert (forall ( (x Int) (y Int)) (=> (and (> x 0) (> y 0) (< x y)  (<= (+ x y) m)) (not (and (= (c x) (c y)) (= (c x) (c (+ x y))  ))))))

(check-sat)
