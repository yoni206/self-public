(set-logic ALL)

(define-fun constval ((d Int)  ) Int 0)
   
(assert (forall ((x Int)  (w Int)) (= w (constval x))))

(check-sat)
