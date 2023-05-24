constant symbol Prop: TYPE;
symbol Prf : Prop → TYPE;

symbol true: Prop;
symbol false: Prop;

//def and : Prop -> Prop -> Prop.
symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 10; // you can even mention that this is associative

// [a,b,c] and (and a b) c --> (and a (and b c)).
rule ($x ∧ $y) ∧ $z ↪ $x ∧ ($y ∧ $z);


symbol A: Prop;
symbol B: Prop;
symbol C: Prop;

// [a,b] prf (and a b) --> prf a.
symbol ∧ₑ₁ [p q] : Prf (p ∧ q) → Prf p;
// And we can set a rewrite rule if we want this to be apply automaticaly when calling tactics like `simplify`
rule Prf ($x ∧ $y) ↪ Prf $x;

// We might be able to use inductive type to define nat.
// see https://lambdapi.readthedocs.io/en/latest/commands.html#inductive
constant symbol nat: TYPE;
symbol 0: nat;
symbol S: nat → nat;

symbol 1 ≔ S 0;
symbol 2 ≔ S (S 0);

// Define a pair (ith-elem, Prop) - we will track the number of time we apply elim 
symbol × : nat → Prop → Prop; notation × infix 10;

symbol ∧ₑ₁0 [p q] : Prf (0 × (p ∧ q)) → Prf (q);
symbol ∧ₑ₁S [i p q] : Prf ((S i) × (p ∧ q)) → Prf (i × q);

assert ⊢ (S (S 0)) × (A ∧ B) : Prop;

// Encode the rewriting rule corresponding to ∧ₑ₁0 and ∧ₑ₁S.
rule 0 × $x ↪ $x;
rule (S $i) × ($x ∧ $y) ↪ $i × $y;

compute 0 × (A ∧ B); // Output: A ∧ B
compute 1 × (A ∧ (B ∧ C)); // Output: B
compute 2 × (A ∧ (B ∧ C)); // Output: C
