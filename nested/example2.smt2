(set-logic ALL)


(declare-datatypes ((NestedDT 0)) (((empty) (insert ( index Int ) (fields (Seq NestedDT) ) ))))
(assert (forall ((x NestedDT) (i Int) (j Int)) (=> (and (<= 0 j) (<= j (seq.len (fields (seq.nth (fields x) i)))) (<= 0 i) (<= i (seq.len (fields x)))) (distinct x (seq.nth (fields (seq.nth (fields x) i)) j )))))
(declare-const dt NestedDT)

; dt = {1, [{2, [dt]}]}
(assert (= (insert 1 (seq.unit (insert 2 (seq.unit dt)))) dt))

(check-sat)
