(* ::Package:: *)

(* ====================================================================== *)
(*  Operad objects and the verification of the operad axioms               *)
(*                                                                        *)
(*  An operad is an Association                                           *)
(*      <| "Name"     -> string,                                          *)
(*         "Elements" -> (n |-> list of the elements of arity n),         *)
(*         "Compose"  -> ({x, i, y} |-> x o_i y),                         *)
(*         "Unit"     -> the identity operation,                          *)
(*         "Equal"    -> optional equality test (default SameQ) |>        *)
(*                                                                        *)
(*  Every operad in this package implements this one interface, so one    *)
(*  verifier (OperadAxiomCheck) serves all of them.                       *)
(*                                                                        *)
(*  This file is read by Operadica.wl inside Operadica`Private`.          *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* examples                                                               *)
(* ---------------------------------------------------------------------- *)

FreeOperad[gens_] :=
  <|
    "Name" -> "Free",
    "Generators" -> gens,
    "Elements" -> Function[n, OpPlanarTrees[gens, n]],
    "Compose" -> OpCompose,
    "Unit" -> OpLeaf
  |>;


AssociativeOperad[] :=
  <|
    "Name" -> "As",
    "Elements" -> Function[n, {n}],
    "Compose" -> Function[{x, i, y}, x + y - 1],
    "Unit" -> 1
  |>;


(* words: {2, 1, 3} stands for the monomial x2 x1 x3 *)
opWordCompose[w_List, i_Integer, v_List] :=
  With[{m = Length[v]},
    Flatten[
      Replace[w, {i -> v + (i - 1), k_Integer /; k > i :> k + m - 1}, {1}]
    ]
  ];

WordOperad[] :=
  <|
    "Name" -> "Words",
    "Elements" -> Function[n, Permutations[Range[n]]],
    "Compose" -> opWordCompose,
    "Unit" -> {1}
  |>;


(* functions set^n -> set as Associations  n-tuple -> value *)
opEndCompose[set_List][f_Association, i_Integer, g_Association] :=
  With[{l = Length[First[Keys[f]]], m = Length[First[Keys[g]]]},
    Association[
      Function[tup,
        tup -> f[Key[
          Join[
            Take[tup, i - 1],
            {g[Key[Take[tup, {i, i + m - 1}]]]},
            Drop[tup, i + m - 1]
          ]
        ]]
      ] /@ Tuples[set, l + m - 1]
    ]
  ];

EndOperad[set_List] :=
  <|
    "Name" -> "End",
    "Set" -> set,
    "Elements" -> Function[n,
      AssociationThread[Tuples[set, n], #] & /@ Tuples[set, Length[set]^n]
    ],
    "Compose" -> opEndCompose[set],
    "Unit" -> AssociationThread[Tuples[set, 1], set],
    "Equal" -> Function[{f, g}, KeySort[f] === KeySort[g]]
  |>;


(* ---------------------------------------------------------------------- *)
(* axioms                                                                 *)
(*                                                                        *)
(*   unit        id o_1 a = a ,   a o_i id = a                            *)
(*   sequential  (a o_i b) o_{i+j-1} c = a o_i (b o_j c)                  *)
(*   parallel    (a o_i b) o_{k+m-1} c = (a o_k c) o_i b   for i < k,     *)
(*               where m is the arity of b                                *)
(* ---------------------------------------------------------------------- *)

Options[OperadAxiomCheck] = {"MinArity" -> 1, "MaxCounterexamples" -> 3};

OperadAxiomCheck[op_Association, maxArity_Integer?Positive, OptionsPattern[]] :=
  Module[{comp, unit, eq, minA, maxBad, elems, checked, failed, bad, note,
      a, b, c, i, j, k, l, m, n},
    comp = op["Compose"];
    unit = op["Unit"];
    eq = Lookup[op, "Equal", SameQ];
    minA = OptionValue["MinArity"];
    maxBad = OptionValue["MaxCounterexamples"];
    elems = Association[Table[n -> op["Elements"][n], {n, minA, maxArity}]];
    checked = <|"Unit" -> 0, "Sequential" -> 0, "Parallel" -> 0|>;
    failed = <|"Unit" -> 0, "Sequential" -> 0, "Parallel" -> 0|>;
    bad = <|"Unit" -> {}, "Sequential" -> {}, "Parallel" -> {}|>;

    note = Function[{axiom, ok, data},
      checked[axiom] = checked[axiom] + 1;
      If[! TrueQ[ok],
        failed[axiom] = failed[axiom] + 1;
        If[Length[bad[axiom]] < maxBad,
          bad[axiom] = Append[bad[axiom], data]
        ]
      ]
    ];

    (* unit *)
    Do[
      Do[
        note["Unit", eq[comp[unit, 1, a], a], {"left", a}];
        Do[
          note["Unit", eq[comp[a, i, unit], a], {"right", a, i}],
          {i, 1, n}
        ],
        {a, elems[n]}
      ],
      {n, minA, maxArity}
    ];

    (* associativity *)
    Do[
      If[l + m + n - 2 <= maxArity,
        Do[
          Do[
            note["Sequential",
              eq[comp[comp[a, i, b], i + j - 1, c], comp[a, i, comp[b, j, c]]],
              {a, i, b, j, c}
            ],
            {i, 1, l}, {j, 1, m}
          ];
          Do[
            note["Parallel",
              eq[comp[comp[a, i, b], k + m - 1, c], comp[comp[a, k, c], i, b]],
              {a, i, b, k, c}
            ],
            {i, 1, l}, {k, i + 1, l}
          ],
          {a, elems[l]}, {b, elems[m]}, {c, elems[n]}
        ]
      ],
      {l, minA, maxArity}, {m, minA, maxArity}, {n, minA, maxArity}
    ];

    <|
      "Operad" -> Lookup[op, "Name", "unnamed"],
      "MaxArity" -> maxArity,
      "Passed" -> (Total[Values[failed]] === 0),
      "Checked" -> checked,
      "Failed" -> failed,
      "Counterexamples" -> bad,
      "Strength" -> "exhaustive over the listed elements, total arity <= " <> ToString[maxArity]
    |>
  ];


Options[OperadAxiomsQ] = Options[OperadAxiomCheck];

OperadAxiomsQ[op_Association, maxArity_Integer?Positive, opts : OptionsPattern[]] :=
  TrueQ[OperadAxiomCheck[op, maxArity, opts]["Passed"]];


(* ---------------------------------------------------------------------- *)
(* algebras over a presented operad                                       *)
(*                                                                        *)
(* For an operad presented by generators and relations, a choice of       *)
(* functions for the generators is an algebra exactly when the relations  *)
(* hold.  Checking the relations is therefore a check in all arities.     *)
(* ---------------------------------------------------------------------- *)

OpAssociativityRelation[m_] :=
  {m[m[OpLeaf, OpLeaf], OpLeaf], m[OpLeaf, m[OpLeaf, OpLeaf]]};


Options[OpAlgebraCheck] = {"Equal" -> SameQ};

OpAlgebraCheck[relations_List, rules_, argTuples_List, OptionsPattern[]] :=
  Module[{eq = OptionValue["Equal"], bad = {}, tried = 0, rel, args},
    Do[
      If[Length[args] === OpArity[First[rel]],
        tried = tried + 1;
        If[
          ! TrueQ[eq[
            OpEvaluate[First[rel], rules, args],
            OpEvaluate[Last[rel], rules, args]
          ]],
          bad = Append[bad, {rel, args}]
        ]
      ],
      {rel, relations}, {args, argTuples}
    ];
    <|
      "Passed" -> (bad === {} && tried > 0),
      "Checked" -> tried,
      "Counterexamples" -> Take[bad, UpTo[3]]
    |>
  ];
