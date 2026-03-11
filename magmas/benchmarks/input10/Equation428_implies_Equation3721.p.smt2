(declare-sort $$unsorted 0)
(declare-fun tptp.op ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X0 $$unsorted) (X1 $$unsorted) (X2 $$unsorted)) (= X0 (tptp.op X0 (tptp.op X1 (tptp.op X0 (tptp.op X0 X2)))))))
(error "Parse Error: benchmarks/input10/Equation428_implies_Equation3721.p:8.38: Unexpected token: '('.")
