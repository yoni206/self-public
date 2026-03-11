(declare-sort $$unsorted 0)
(declare-fun tptp.op ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X0 $$unsorted) (X1 $$unsorted) (X2 $$unsorted) (X3 $$unsorted)) (= X0 (tptp.op (tptp.op (tptp.op (tptp.op X1 X1) X0) X1) X2))))
(error "Parse Error: benchmarks/input8/Equation3144_implies_Equation1490.p:8.31: Unexpected token: '('.")
