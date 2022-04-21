(set-logic ALL)


(declare-datatypes ((NestedDT 0)) (
((empty) (insert ( index Int ) (fields (Seq NestedDT) ) ))
))

(declare-const dt NestedDT)

; dt = [1, [dt]]
(assert (= (insert 1 (seq.unit dt)) dt))
(check-sat)
