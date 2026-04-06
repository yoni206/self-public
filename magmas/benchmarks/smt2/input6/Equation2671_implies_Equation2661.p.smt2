(declare-sort $$unsorted 0)
(declare-fun tptp.op ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X0 $$unsorted) (X1 $$unsorted) (X2 $$unsorted) (X3 $$unsorted)) (= X0 (tptp.op (tptp.op (tptp.op X0 X1) (tptp.op X1 X0)) X2))))
(error "Parse Error: benchmarks/input6/Equation2671_implies_Equation2661.p:8.49: Unexpected token: '-'.")
