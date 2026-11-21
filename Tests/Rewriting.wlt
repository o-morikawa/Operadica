(* Rewriting: presented operads, normal forms, local confluence *)

VerificationTest[
  OpNormalForm[
    m[m[m[OpLeaf, OpLeaf], OpLeaf], OpLeaf],
    {m[m[a_, b_], c_] :> m[a, m[b, c]]}
  ],
  m[OpLeaf, m[OpLeaf, m[OpLeaf, OpLeaf]]],
  TestID -> "Rewriting-normal-form"
]

VerificationTest[
  Sort[OpRewriteSteps[
    m[m[m[OpLeaf, OpLeaf], OpLeaf], OpLeaf],
    {m[m[a_, b_], c_] :> m[a, m[b, c]]}
  ]],
  Sort[{
    m[m[OpLeaf, OpLeaf], m[OpLeaf, OpLeaf]],
    m[m[OpLeaf, m[OpLeaf, OpLeaf]], OpLeaf]
  }],
  TestID -> "Rewriting-one-step"
]

(* associativity: the only critical pair is the pentagon, in arity 4 *)

VerificationTest[
  OpLocallyConfluentQ[{m -> 2}, {m[m[a_, b_], c_] :> m[a, m[b, c]]}, 5],
  True,
  TestID -> "Rewriting-As-confluent"
]

(* the quotient has one operation in each arity: it is the operad As *)

VerificationTest[
  With[{as = QuotientOperad[{m -> 2}, {m[m[a_, b_], c_] :> m[a, m[b, c]]}]},
    Table[Length[as["Elements"][n]], {n, 1, 6}]
  ],
  {1, 1, 1, 1, 1, 1},
  TestID -> "Rewriting-As-dimensions"
]

VerificationTest[
  OperadAxiomsQ[QuotientOperad[{m -> 2}, {m[m[a_, b_], c_] :> m[a, m[b, c]]}], 5],
  True,
  TestID -> "Rewriting-As-axioms"
]

(* a system that is not confluent is detected at the arity of its critical pair *)

VerificationTest[
  With[{rules = {m[m[a_, b_], c_] :> m[a, m[b, c]], m[a_, m[b_, c_]] :> t[a, b, c]}},
    {
      OpLocallyConfluentQ[{m -> 2, t -> 3}, rules, 3],
      OpLocallyConfluentQ[{m -> 2, t -> 3}, rules, 4]
    }
  ],
  {True, False},
  TestID -> "Rewriting-nonconfluent-detected"
]
