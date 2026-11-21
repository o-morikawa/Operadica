(* Trees: planar trees and grafting (the free nonsymmetric operad) *)

VerificationTest[
  OpTreeQ[m[m[OpLeaf, OpLeaf], OpLeaf]],
  True,
  TestID -> "Trees-TreeQ-true"
]

VerificationTest[
  OpTreeQ[m[x, OpLeaf]],
  False,
  TestID -> "Trees-TreeQ-false"
]

VerificationTest[
  OpLeafPositions[m[m[OpLeaf, OpLeaf], OpLeaf]],
  {{1, 1}, {1, 2}, {2}},
  TestID -> "Trees-leaf-positions"
]

VerificationTest[
  OpLeafPositions[OpLeaf],
  {{}},
  TestID -> "Trees-leaf-positions-root"
]

VerificationTest[
  {OpArity[OpLeaf], OpArity[m[m[OpLeaf, OpLeaf], OpLeaf]], OpArity[mu[3][OpLeaf, OpLeaf, OpLeaf]], OpArity[u[]]},
  {1, 3, 3, 0},
  TestID -> "Trees-arity"
]

VerificationTest[
  OpCorolla[m, 3],
  m[OpLeaf, OpLeaf, OpLeaf],
  TestID -> "Trees-corolla"
]

(* partial composition *)

VerificationTest[
  OpCompose[m[OpLeaf, OpLeaf], 1, m[OpLeaf, OpLeaf]],
  m[m[OpLeaf, OpLeaf], OpLeaf],
  TestID -> "Trees-compose-1"
]

VerificationTest[
  OpCompose[m[OpLeaf, OpLeaf], 2, m[OpLeaf, OpLeaf]],
  m[OpLeaf, m[OpLeaf, OpLeaf]],
  TestID -> "Trees-compose-2"
]

VerificationTest[
  OpCompose[m[m[OpLeaf, OpLeaf], OpLeaf], 3, t[OpLeaf, OpLeaf, OpLeaf]],
  m[m[OpLeaf, OpLeaf], t[OpLeaf, OpLeaf, OpLeaf]],
  TestID -> "Trees-compose-nested"
]

VerificationTest[
  {OpCompose[OpLeaf, 1, m[OpLeaf, OpLeaf]], OpCompose[m[OpLeaf, OpLeaf], 2, OpLeaf]},
  {m[OpLeaf, OpLeaf], m[OpLeaf, OpLeaf]},
  TestID -> "Trees-compose-unit"
]

VerificationTest[
  OpCompose[m[OpLeaf, OpLeaf], 3, OpLeaf],
  $Failed,
  {OpCompose::arity},
  TestID -> "Trees-compose-out-of-range"
]

(* full composition *)

VerificationTest[
  OpComposeAll[m[OpLeaf, OpLeaf], {m[OpLeaf, OpLeaf], OpLeaf}],
  m[m[OpLeaf, OpLeaf], OpLeaf],
  TestID -> "Trees-composeall"
]

VerificationTest[
  OpComposeAll[OpLeaf, {m[OpLeaf, OpLeaf]}],
  m[OpLeaf, OpLeaf],
  TestID -> "Trees-composeall-root"
]

VerificationTest[
  OpComposeAll[m[OpLeaf, OpLeaf], {m[OpLeaf, OpLeaf], m[OpLeaf, OpLeaf]}] ===
    OpCompose[OpCompose[m[OpLeaf, OpLeaf], 2, m[OpLeaf, OpLeaf]], 1, m[OpLeaf, OpLeaf]],
  True,
  TestID -> "Trees-composeall-from-partial"
]

(* enumeration: Catalan numbers for one binary generator *)

VerificationTest[
  Table[Length[OpPlanarTrees[{m -> 2}, n]], {n, 1, 7}],
  {1, 1, 2, 5, 14, 42, 132},
  TestID -> "Trees-count-Catalan"
]

(* one generator in each arity >= 2: faces of the associahedron,
   counted by the little Schroeder numbers *)

VerificationTest[
  Table[Length[OpPlanarTrees[Table[mu[k] -> k, {k, 2, 6}], n]], {n, 2, 6}],
  {1, 3, 11, 45, 197},
  TestID -> "Trees-count-Schroeder"
]

VerificationTest[
  AllTrue[OpPlanarTrees[{m -> 2, t -> 3}, 5], OpTreeQ[#] && OpArity[#] === 5 &],
  True,
  TestID -> "Trees-enumeration-arity"
]

VerificationTest[
  OpPlanarTrees[{m -> 1}, 3],
  $Failed,
  {OpPlanarTrees::gens},
  TestID -> "Trees-enumeration-unary-rejected"
]

(* trees as functions *)

VerificationTest[
  OpEvaluate[m[m[OpLeaf, OpLeaf], OpLeaf], {m -> Plus}, {1, 2, 3}],
  6,
  TestID -> "Trees-evaluate-plus"
]

VerificationTest[
  {
    OpEvaluate[m[m[OpLeaf, OpLeaf], OpLeaf], {m -> Subtract}, {1, 2, 3}],
    OpEvaluate[m[OpLeaf, m[OpLeaf, OpLeaf]], {m -> Subtract}, {1, 2, 3}]
  },
  {-4, 2},
  TestID -> "Trees-evaluate-subtract"
]

VerificationTest[
  OpEvaluate[OpLeaf, {m -> Plus}, {7}],
  7,
  TestID -> "Trees-evaluate-identity"
]

VerificationTest[
  OpEvaluate[m[OpLeaf, OpLeaf], {m -> Plus}, {1, 2, 3}],
  $Failed,
  {OpEvaluate::arity},
  TestID -> "Trees-evaluate-arity"
]

(* subtrees *)

VerificationTest[
  {
    OpSubtree[m[m[OpLeaf, OpLeaf], t[OpLeaf, OpLeaf, OpLeaf]], {2}],
    OpSubtree[m[OpLeaf, OpLeaf], {}],
    OpReplaceSubtree[m[m[OpLeaf, OpLeaf], OpLeaf], {1}, OpLeaf],
    OpReplaceSubtree[m[OpLeaf, OpLeaf], {}, OpLeaf]
  },
  {t[OpLeaf, OpLeaf, OpLeaf], m[OpLeaf, OpLeaf], m[OpLeaf, OpLeaf], OpLeaf},
  TestID -> "Trees-subtree"
]
