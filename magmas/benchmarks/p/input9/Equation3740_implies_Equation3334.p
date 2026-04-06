fof(a1, axiom,
    ! [X0, X1, X2] :
        (op(X0,X1) = op(op(X0,X2),op(X2,X1)))
).

fof(conjecture0, conjecture,
    ! [X0, X1, X2] :
        (op(X0,X1) = op(X0,op(X2,op(X2,X1))))
).
