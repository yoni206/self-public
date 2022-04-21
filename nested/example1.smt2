(set-logic ALL)
;{0, [{1, []},  {2, [{3, []}]}, {4, []}]}

(declare-datatypes ((NestedDT 0)) (
((empty) (insert ( index Int ) ( seq (Seq NestedDT) ) ))
))

(declare-const dt NestedDT)
; dt = [1, [dt]]
(assert (= (insert 1 (seq.unit dt)) dt))
(check-sat)
