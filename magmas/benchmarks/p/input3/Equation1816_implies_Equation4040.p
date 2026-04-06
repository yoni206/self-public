fof(a1, axiom,
    ! [X0, X1, X2, X3] :
        (X0 = op(op(X1,X2),op(op(X3,X2),X0)))
).

fof(conjecture0, conjecture,
    ! [X0, X1, X2, X3] :
        (op(X0,X1) = op(op(X2,op(X3,X0)),X1))
).
