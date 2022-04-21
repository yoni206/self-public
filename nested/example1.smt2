(set-logic ALL)


(declare-datatypes ((NestedDT 0)) (
((empty) (insert ( index Int ) ( seq (Seq NestedDT) ) ))
))
;an example of a legit datatype:
;{0, [{1, []},  {2, [{3, []}]}, {4, []}]}


(declare-const dt NestedDT)

; non-legit datatype:
; dt = [1, [dt]]
(assert (= (insert 1 (seq.unit dt)) dt))
(check-sat)
