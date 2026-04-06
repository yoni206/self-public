fof(a1, axiom,
    ! [X0, X1] :
        (X0 = op(X0,op(X1,op(X0,X1))))
).

fof(conjecture0, conjecture,
    ! [X0, X1] :
        (X0 = op(X0,op(op(X1,op(X0,X1)),X0)))
).
