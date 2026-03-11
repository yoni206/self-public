(set-logic QF_ABV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const _0 (_ BitVec 32))

(assert (= _0 (_ bv0 32)))

(assert (= _0 (bvsrem y x)))
(assert
  (not (= _0 (bvsrem (bvsub _0 y) x))))
(check-sat)
