fof(a1, axiom,
    ! [X0, X1, X2] :
        (X0 = op(X1,op(op(X1,op(X2,X0)),X0)))
).

fof(conjecture0, conjecture,
    ! [X0, X1, X2] :
        (X0 = op(op(op(X1,X2),X1),op(X0,X0)))
).
