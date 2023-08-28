(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))


(define-fun initial_lemma_1 () Bool (= (bvand (bvor (bvneg s) s) t)  t))
(define-fun initial_lemma_2 () Bool (=> (= s (_ bv0 4)) (= t (_ bv0 4))))
(define-fun initial_lemma_3 () Bool (=> (= s (_ bv1 4)) (= t x)))
(define-fun initial_lemma_4 () Bool (=> (= s (bvnot (_ bv0 4))) (= t (bvneg x))))
(define-fun A2 () Bool (bvule t (bvor (bvneg s) s)))

(assert initial_lemma_1)
(assert (not A2))

(check-sat)
