(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Operads`                                                     *)
(*                                                                        *)
(*  Operad objects and the verification of the operad axioms.              *)
(*                                                                        *)
(*  An operad is an Association                                           *)
(*      <| "Name"     -> string,                                          *)
(*         "Elements" -> (n |-> list of the elements of arity n),         *)
(*         "Compose"  -> ({x, i, y} |-> x o_i y),                         *)
(*         "Unit"     -> the identity operation,                          *)
(*         "Equal"    -> optional equality test (default SameQ),          *)
(*         "Action"   -> optional ({x, s} |-> x.s), the right action of   *)
(*                       the symmetric group (symmetric operads) |>       *)
(*                                                                        *)
(*  Every operad in Operadica implements this one interface, so the same  *)
(*  two verifiers serve all of them.                                      *)
(*                                                                        *)
(*  Conventions for symmetric operads                                     *)
(*  (checked in reference/operad_reference.py):                           *)
(*    a permutation s is the list {s(1), ..., s(n)};                      *)
(*    the action is a right action: (x.s).t = x.(s t), (s t)(j) = s(t(j)); *)
(*    on functions, (f.s)(x1, ..., xn) = f(x_{s^-1(1)}, ..., x_{s^-1(n)}); *)
(*    equivariance: (a.s) o_i (b.t) = (a o_{s(i)} b).(s o_i t),           *)
(*    with s o_i t = PermutationCompose[s, i, t].                         *)
(*                                                                        *)
(*  Layer: operad.  Depends on: Trees.                                    *)
(* ====================================================================== *)

BeginPackage["Operadica`Operads`", {"Operadica`Trees`"}];

FreeOperad::usage = "FreeOperad[{h1 -> k1, ...}] gives the free nonsymmetric operad on generators hi of arity ki. An operad is an Association with keys \"Name\", \"Elements\" (arity -> list of elements), \"Compose\" (a function of {x, i, y} giving the partial composition of y into input i of x), \"Unit\", and optionally \"Equal\" and \"Action\".";

AssociativeOperad::usage = "AssociativeOperad[] gives the nonsymmetric associative operad: one operation in each arity n >= 1, represented by the integer n.";

CommutativeOperad::usage = "CommutativeOperad[] gives the commutative operad as a symmetric operad: one operation in each arity n >= 1, represented by the integer n, with trivial action of the symmetric group.";

WordOperad::usage = "WordOperad[] gives the associative operad as a symmetric operad: an operation of arity n is a word in x1, ..., xn using each variable once, represented by a permutation of {1, ..., n}. Composition is substitution of words.";

EndOperad::usage = "EndOperad[set] gives the endomorphism operad of a finite set as a symmetric operad: an operation of arity n is a function set^n -> set, represented by an Association from n-tuples to elements.";

OperadAxiomCheck::usage = "OperadAxiomCheck[op, maxArity] checks the unit axiom and the sequential and parallel associativity axioms of partial composition, for all compositions of total arity at most maxArity. By default it runs over op[\"Elements\"]; the option \"Elements\" -> <|n -> list, ...|> supplies the elements to test instead. It returns an Association with the keys \"Passed\", \"Checked\", \"Failed\", \"Counterexamples\" and \"Strength\".";

OperadAxiomsQ::usage = "OperadAxiomsQ[op, maxArity] gives True if OperadAxiomCheck finds no violation.";

OperadEquivarianceCheck::usage = "OperadEquivarianceCheck[op, maxArity] checks, for an operad with an \"Action\", that the action is a right action of the symmetric groups and that partial composition is equivariant: (a.s) o_i (b.t) = (a o_{s(i)} b).(s o_i t). It takes the same options and returns the same keys as OperadAxiomCheck.";

OperadEquivariantQ::usage = "OperadEquivariantQ[op, maxArity] gives True if OperadEquivarianceCheck finds no violation.";

PermutationCompose::usage = "PermutationCompose[s, i, t] gives the block permutation s o_i t of {1, ..., m + n - 1} obtained from permutations s of {1, ..., m} and t of {1, ..., n}: the i-th point is replaced by a block of n points permuted by t.";

OpAssociativityRelation::usage = "OpAssociativityRelation[m] gives the pair of trees {m[m[OpLeaf, OpLeaf], OpLeaf], m[OpLeaf, m[OpLeaf, OpLeaf]]}.";

OpAlgebraCheck::usage = "OpAlgebraCheck[relations, rules, argTuples] checks that each relation {lhsTree, rhsTree} holds when the generators are interpreted by rules and both sides are applied to each tuple of arguments of the right length. The option \"Equal\" sets the equality test (default SameQ). It returns an Association with the keys \"Passed\", \"Checked\" and \"Counterexamples\".";

Begin["`Private`"];

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


CommutativeOperad[] :=
  <|
    "Name" -> "Com",
    "Elements" -> Function[n, {n}],
    "Compose" -> Function[{x, i, y}, x + y - 1],
    "Unit" -> 1,
    "Action" -> Function[{x, s}, x]
  |>;


(* words: {2, 1, 3} stands for the monomial x2 x1 x3;  (w.s)_k = s^-1(w_k) *)
wordCompose[w_List, i_Integer, v_List] :=
  With[{m = Length[v]},
    Flatten[
      Replace[w, {i -> v + (i - 1), k_Integer /; k > i :> k + m - 1}, {1}]
    ]
  ];

wordAct[w_List, s_List] := Ordering[s][[w]];

WordOperad[] :=
  <|
    "Name" -> "Words",
    "Elements" -> Function[n, Permutations[Range[n]]],
    "Compose" -> wordCompose,
    "Unit" -> {1},
    "Action" -> wordAct
  |>;


(* functions set^n -> set as Associations  n-tuple -> value *)
endCompose[set_List][f_Association, i_Integer, g_Association] :=
  With[{l = Length[First[Keys[f]]], m = Length[First[Keys[g]]]},
    Association[
      Map[
        Function[tup,
          tup -> Lookup[f, Key[
            Join[
              Take[tup, i - 1],
              {Lookup[g, Key[Take[tup, {i, i + m - 1}]]]},
              Drop[tup, i + m - 1]
            ]
          ]]
        ],
        Tuples[set, l + m - 1]
      ]
    ]
  ];

(* (f.s)(x1, ..., xn) = f(x_{s^-1(1)}, ..., x_{s^-1(n)}) *)
endAct[set_List][f_Association, s_List] :=
  With[{sinv = Ordering[s]},
    Association[
      Map[Function[tup, tup -> Lookup[f, Key[tup[[sinv]]]]], Tuples[set, Length[s]]]
    ]
  ];

EndOperad[set_List] :=
  <|
    "Name" -> "End",
    "Set" -> set,
    "Elements" -> Function[n,
      Map[Function[vals, AssociationThread[Tuples[set, n], vals]], Tuples[set, Length[set]^n]]
    ],
    "Compose" -> endCompose[set],
    "Unit" -> AssociationThread[Tuples[set, 1], set],
    "Action" -> endAct[set],
    "Equal" -> Function[{f, g}, KeySort[f] === KeySort[g]]
  |>;


(* ---------------------------------------------------------------------- *)
(* the symmetric groups                                                   *)
(* ---------------------------------------------------------------------- *)

(* rho(phi(j))    = psi(s(j))          for j != i
   rho(i - 1 + r) = s(i) + t(r) - 1    for r = 1..n
   phi(j) = j (j < i), j + n - 1 (j > i);  psi(k) = k (k < s(i)), k + n - 1 (k > s(i)) *)
PermutationCompose[s_List, i_Integer, t_List] :=
  Module[{m = Length[s], n = Length[t], si, rho, j, r, k},
    si = s[[i]];
    rho = ConstantArray[0, m + n - 1];
    Do[
      If[j =!= i,
        k = s[[j]];
        rho[[If[j < i, j, j + n - 1]]] = If[k < si, k, k + n - 1]
      ],
      {j, 1, m}
    ];
    Do[
      rho[[i - 1 + r]] = si + t[[r]] - 1,
      {r, 1, n}
    ];
    rho
  ];


(* ---------------------------------------------------------------------- *)
(* axioms                                                                 *)
(*                                                                        *)
(*   unit        id o_1 a = a ,   a o_i id = a                            *)
(*   sequential  (a o_i b) o_{i+j-1} c = a o_i (b o_j c)                  *)
(*   parallel    (a o_i b) o_{k+m-1} c = (a o_k c) o_i b   for i < k,     *)
(*               where m is the arity of b                                *)
(* ---------------------------------------------------------------------- *)

checkOptions = {"MinArity" -> 1, "MaxCounterexamples" -> 3, "Elements" -> Automatic};

(* the elements to test: the operad's own enumeration or a supplied table *)
elementTable[op_, minA_, maxArity_, Automatic] :=
  Association[Table[n -> op["Elements"][n], {n, minA, maxArity}]];

elementTable[op_, minA_, maxArity_, given_Association] :=
  Association[Table[n -> Lookup[given, n, {}], {n, minA, maxArity}]];

strengthNote[op_, maxArity_, Automatic] :=
  Lookup[op, "ElementsNote", "exhaustive over the listed elements"] <>
    ", total arity <= " <> ToString[maxArity];

strengthNote[op_, maxArity_, _Association] :=
  "over the supplied elements, total arity <= " <> ToString[maxArity];


Options[OperadAxiomCheck] = checkOptions;

OperadAxiomCheck[op_Association, maxArity_Integer?Positive, OptionsPattern[]] :=
  Module[{comp, unit, eq, minA, maxBad, elems, checked, failed, bad, note,
      a, b, c, i, j, k, l, m, n},
    comp = op["Compose"];
    unit = op["Unit"];
    eq = Lookup[op, "Equal", SameQ];
    minA = OptionValue["MinArity"];
    maxBad = OptionValue["MaxCounterexamples"];
    elems = elementTable[op, minA, maxArity, OptionValue["Elements"]];
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
      "Strength" -> strengthNote[op, maxArity, OptionValue["Elements"]]
    |>
  ];


Options[OperadAxiomsQ] = checkOptions;

OperadAxiomsQ[op_Association, maxArity_Integer?Positive, opts : OptionsPattern[]] :=
  TrueQ[OperadAxiomCheck[op, maxArity, opts]["Passed"]];


(* ---------------------------------------------------------------------- *)
(* equivariance                                                           *)
(*                                                                        *)
(*   action        x.id = x ,   (x.s).t = x.(s t)                         *)
(*   equivariance  (a.s) o_i (b.t) = (a o_{s(i)} b).(s o_i t)             *)
(* ---------------------------------------------------------------------- *)

OperadEquivarianceCheck::noaction = "The operad `1` has no \"Action\"; it is not given as a symmetric operad.";

Options[OperadEquivarianceCheck] = checkOptions;

OperadEquivarianceCheck[op_Association, maxArity_Integer?Positive, OptionsPattern[]] :=
  Module[{comp, act, eq, minA, maxBad, elems, perms, checked, failed, bad, note,
      a, b, i, m, n, s, t},
    If[! KeyExistsQ[op, "Action"],
      Message[OperadEquivarianceCheck::noaction, Lookup[op, "Name", "unnamed"]];
      $Failed,

      comp = op["Compose"];
      act = op["Action"];
      eq = Lookup[op, "Equal", SameQ];
      minA = OptionValue["MinArity"];
      maxBad = OptionValue["MaxCounterexamples"];
      elems = elementTable[op, minA, maxArity, OptionValue["Elements"]];
      perms = Association[Table[n -> Permutations[Range[n]], {n, 0, maxArity}]];
      checked = <|"Action" -> 0, "Equivariance" -> 0|>;
      failed = <|"Action" -> 0, "Equivariance" -> 0|>;
      bad = <|"Action" -> {}, "Equivariance" -> {}|>;

      note = Function[{axiom, ok, data},
        checked[axiom] = checked[axiom] + 1;
        If[! TrueQ[ok],
          failed[axiom] = failed[axiom] + 1;
          If[Length[bad[axiom]] < maxBad,
            bad[axiom] = Append[bad[axiom], data]
          ]
        ]
      ];

      (* right action *)
      Do[
        Do[
          note["Action", eq[act[a, Range[m]], a], {"identity", a}];
          Do[
            note["Action", eq[act[act[a, s], t], act[a, s[[t]]]], {"product", a, s, t}],
            {s, perms[m]}, {t, perms[m]}
          ],
          {a, elems[m]}
        ],
        {m, minA, maxArity}
      ];

      (* equivariance of partial composition *)
      Do[
        If[m + n - 1 <= maxArity,
          Do[
            note["Equivariance",
              eq[
                comp[act[a, s], i, act[b, t]],
                act[comp[a, s[[i]], b], PermutationCompose[s, i, t]]
              ],
              {a, s, i, b, t}
            ],
            {a, elems[m]}, {b, elems[n]}, {s, perms[m]}, {t, perms[n]}, {i, 1, m}
          ]
        ],
        {m, minA, maxArity}, {n, minA, maxArity}
      ];

      <|
        "Operad" -> Lookup[op, "Name", "unnamed"],
        "MaxArity" -> maxArity,
        "Passed" -> (Total[Values[failed]] === 0),
        "Checked" -> checked,
        "Failed" -> failed,
        "Counterexamples" -> bad,
        "Strength" -> strengthNote[op, maxArity, OptionValue["Elements"]]
      |>
    ]
  ];


Options[OperadEquivariantQ] = checkOptions;

OperadEquivariantQ[op_Association, maxArity_Integer?Positive, opts : OptionsPattern[]] :=
  With[{r = OperadEquivarianceCheck[op, maxArity, opts]},
    AssociationQ[r] && TrueQ[r["Passed"]]
  ];


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

End[];

EndPackage[];
