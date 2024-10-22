(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const _0 (_ BitVec 8))

(assert (= _0 #x00))

;(assert (bvslt _0 x))
;(assert (bvslt y _0))
(assert (= _0 (bvsrem y x)))
(assert
  (not (= _0 (bvsrem (bvsub _0 y) x))))
(check-sat)
