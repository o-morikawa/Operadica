(* Operads: the common interface and the axiom verifier *)

(* free operads satisfy the axioms by construction; this tests the code *)

VerificationTest[
  OperadAxiomsQ[FreeOperad[{m -> 2}], 5],
  True,
  TestID -> "Operads-free-binary"
]

VerificationTest[
  OperadAxiomsQ[FreeOperad[{m -> 2, t -> 3}], 5],
  True,
  TestID -> "Operads-free-binary-ternary"
]

VerificationTest[
  OperadAxiomsQ[AssociativeOperad[], 6],
  True,
  TestID -> "Operads-As"
]

(* the associative operad as words: n! operations in arity n *)

VerificationTest[
  Table[Length[WordOperad[]["Elements"][n]], {n, 1, 5}],
  {1, 2, 6, 24, 120},
  TestID -> "Operads-words-count"
]

VerificationTest[
  {
    WordOperad[]["Compose"][{2, 1}, 1, {1, 2}],
    WordOperad[]["Compose"][{2, 1}, 2, {2, 1}],
    WordOperad[]["Compose"][{1, 3, 2}, 3, {2, 1}]
  },
  {{3, 1, 2}, {3, 2, 1}, {1, 4, 3, 2}},
  TestID -> "Operads-words-compose"
]

VerificationTest[
  OperadAxiomsQ[WordOperad[], 4],
  True,
  TestID -> "Operads-words-axioms"
]

(* endomorphism operad of a two-element set *)

VerificationTest[
  Table[Length[EndOperad[{0, 1}]["Elements"][n]], {n, 1, 3}],
  {4, 16, 256},
  TestID -> "Operads-End-count"
]

VerificationTest[
  With[{and = <|{0, 0} -> 0, {0, 1} -> 0, {1, 0} -> 0, {1, 1} -> 1|>, end = EndOperad[{0, 1}]},
    With[{and3 = end["Compose"][and, 1, and]},
      {and3[Key[{1, 1, 1}]], and3[Key[{1, 0, 1}]], Length[and3]}
    ]
  ],
  {1, 0, 8},
  TestID -> "Operads-End-compose"
]

VerificationTest[
  OperadAxiomsQ[EndOperad[{0, 1}], 3],
  True,
  TestID -> "Operads-End-axioms"
]

(* the verifier reports what it did *)

VerificationTest[
  With[{r = OperadAxiomCheck[AssociativeOperad[], 4]},
    {r["Passed"], Sort[Keys[r["Checked"]]], AllTrue[Values[r["Checked"]], # > 0 &], Total[Values[r["Failed"]]]}
  ],
  {True, {"Parallel", "Sequential", "Unit"}, True, 0},
  TestID -> "Operads-check-report"
]

(* a composition that is not associative or unital is caught *)

VerificationTest[
  OperadAxiomsQ[
    <|"Name" -> "broken", "Elements" -> Function[n, {n}], "Compose" -> Function[{x, i, y}, x + y], "Unit" -> 1|>,
    4
  ],
  False,
  TestID -> "Operads-broken-detected"
]

VerificationTest[
  With[{r = OperadAxiomCheck[
      <|"Name" -> "broken", "Elements" -> Function[n, {n}], "Compose" -> Function[{x, i, y}, x + y], "Unit" -> 1|>,
      3]},
    {r["Passed"], r["Failed"]["Unit"] > 0, Length[r["Counterexamples"]["Unit"]] > 0}
  ],
  {False, True, True},
  TestID -> "Operads-broken-counterexamples"
]

(* algebras: a relation checked on all arguments is a proof for that set *)

VerificationTest[
  OpAssociativityRelation[m],
  {m[m[OpLeaf, OpLeaf], OpLeaf], m[OpLeaf, m[OpLeaf, OpLeaf]]},
  TestID -> "Operads-associativity-relation"
]

VerificationTest[
  OpAlgebraCheck[{OpAssociativityRelation[m]}, {m -> Max}, Tuples[Range[0, 2], 3]]["Passed"],
  True,
  TestID -> "Operads-algebra-max"
]

VerificationTest[
  OpAlgebraCheck[{OpAssociativityRelation[m]}, {m -> Subtract}, Tuples[Range[0, 2], 3]]["Passed"],
  False,
  TestID -> "Operads-algebra-subtract"
]

VerificationTest[
  OpAlgebraCheck[
    {OpAssociativityRelation[m]},
    {m -> Function[{a, b}, Mod[a + b, 3]]},
    Tuples[Range[0, 2], 3]
  ]["Checked"],
  27,
  TestID -> "Operads-algebra-Z3"
]
