(set-logic ALL)
(declare-const ls (Seq Int))
(assert (< (seq.len ls) 0))
(check-sat)
