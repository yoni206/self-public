fof(a1, axiom,
    ! [X0, X1, X2] :
        (X0 = op(op(X0,X0),op(op(X1,X0),X2)))
).

fof(conjecture0, conjecture,
    ! [X0, X1, X2] :
        (X0 = op(op(X0,op(op(X0,X1),X2)),X0))
).
