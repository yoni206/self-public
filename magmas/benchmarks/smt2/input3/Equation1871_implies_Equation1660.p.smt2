(declare-sort $$unsorted 0)
(declare-fun tptp.op ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X0 $$unsorted) (X1 $$unsorted) (X2 $$unsorted) (X3 $$unsorted)) (= X0 (tptp.op (tptp.op X0 (tptp.op X1 X2)) (tptp.op X1 X0)))))
(error "Parse Error: benchmarks/input3/Equation1871_implies_Equation1660.p:8.31: Unexpected token: '('.")
