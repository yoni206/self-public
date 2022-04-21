(set-logic ALL)


(declare-datatypes ((NestedDT 0)) (((empty) (insert ( index Int ) (fields (Seq NestedDT) ) ))))
(assert (forall ((x NestedDT) (i Int)) (=> (and (<= 0 i) (<= i (seq.len (fields x)))) (distinct x (seq.nth (fields x) i)))))

(declare-const dt NestedDT)

(assert (= (insert 1 (seq.unit (insert 2 (seq.unit dt)))) dt))

(check-sat)
