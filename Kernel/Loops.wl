(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`Loops`                                                       *)
(*                                                                        *)
(*  The little n-cubes act on n-fold loop spaces: the statement that the   *)
(*  recognition theorem turns around.                                     *)
(*                                                                        *)
(*  A point of the n-fold loop space of Y is a map g from the unit n-cube  *)
(*  to Y that sends the boundary to the base point; here a loop is         *)
(*  anything that can be applied to a point t (a list of n numbers) and    *)
(*  gives LoopBase on the boundary.  A configuration c of k little cubes   *)
(*  acts by                                                               *)
(*                                                                        *)
(*    theta(c; g1, .., gk)(t) = gi(ci^(-1)(t))   if t lies inside the cube *)
(*                              the base point   otherwise.               *)
(*                                                                        *)
(*  For n = 1 the configuration {[0, 1/2], [1/2, 1]} is the composition    *)
(*  of loops.  The two ways to compose three loops are two different       *)
(*  configurations of three intervals, joined by a path of configurations: *)
(*  associativity up to homotopy.  For n >= 2 a path of configurations     *)
(*  exchanges two cubes: commutativity up to homotopy (Eckmann-Hilton).    *)
(*                                                                        *)
(*  The unit X -> Omega^n Sigma^n X, x -> (t -> [t, x]), then gives May's  *)
(*  approximation map C_n X -> Omega^n Sigma^n X.                         *)
(*                                                                        *)
(*  The loops built from generic loops are piecewise affine on the grid of *)
(*  the endpoints of the cubes, so that two of them are compared at n + 1  *)
(*  points of every cell of the grid: for given configurations with exact  *)
(*  endpoints this is a proof at all points off the grid.                  *)
(*                                                                        *)
(*  Checked in reference/loops_reference.py.                              *)
(*                                                                        *)
(*  Layer: operad.  Depends on: LittleCubes.                              *)
(* ====================================================================== *)

BeginPackage["Operadica`Loops`", {"Operadica`LittleCubes`"}];

LoopBase::usage = "LoopBase is the base point: the value of a loop on the boundary of the unit cube and outside the little cubes.";

GenericLoop::usage = "GenericLoop[name] is a generic point of an n-fold loop space: the map from the unit n-cube whose value at an inner point t (a list of n numbers) is name[t], and LoopBase on the boundary.";

LoopAction::usage = "LoopAction[c][g1, ..., gk] is the n-fold loop theta(c; g1, ..., gk) given by the action of the configuration c of k little n-cubes on the loops g1, ..., gk: at a point inside the i-th cube its value is that of gi at the corresponding point of the unit cube, and it is LoopBase outside the cubes. LoopAction[c][g1, ..., gk][t] evaluates it at the point t.";

SuspensionPoint::usage = "SuspensionPoint[t, x] is the point [t, x] of the n-fold suspension of X, for a point t inside the unit n-cube and a point x of X.";

SuspensionUnit::usage = "SuspensionUnit[x] is the n-fold loop t -> SuspensionPoint[t, x] of the n-fold suspension of X: the unit X -> Omega^n Sigma^n X.";

ApproximationMap::usage = "ApproximationMap[c, {x1, ..., xk}] is the image in Omega^n Sigma^n X of the configuration c of k little n-cubes with the labels x1, ..., xk in X: LoopAction[c] applied to the loops SuspensionUnit[xi]. This is May's map C_n X -> Omega^n Sigma^n X.";

LittleCubesComposeAll::usage = "LittleCubesComposeAll[c, {d1, ..., dk}] inserts the configuration di into the i-th cube of the configuration c, for all i.";

LoopSamplePoints::usage = "LoopSamplePoints[c] gives n + 1 affinely independent points in every cell of the grid formed by the endpoints of the cubes in the list c (the cubes of one or of several configurations).";

LoopEqualQ::usage = "LoopEqualQ[g, h, c] gives True if the loops g and h have the same value at all the points LoopSamplePoints[c]. For loops built with LoopAction from generic loops, with the endpoints of all the cubes involved among those of c, this proves that g and h agree at every point off the grid.";

SwapPath::usage = "SwapPath[n][s] gives, for n >= 2 and 0 <= s <= 2, a configuration of two little n-cubes whose centres move around a square in the first two directions. SwapPath[n][1] is SwapPath[n][0] with the two cubes exchanged, and SwapPath[n][2] is SwapPath[n][0]: half of the path is a homotopy between the products a b and b a of an n-fold loop space, and the whole path is the double braiding.";

Begin["`Private`"];

boundaryQ[t_List] := AnyTrue[t, Function[v, v <= 0 || v >= 1]];

GenericLoop[name_][t_List] := If[boundaryQ[t], LoopBase, name[t]];

SuspensionUnit[x_][t_List] := If[boundaryQ[t], LoopBase, SuspensionPoint[t, x]];

LoopAction[c_List][gs___][t_List] :=
  With[{
      hit = SelectFirst[
        Range[Length[c]],
        Function[i,
          AllTrue[Range[Length[t]], Function[mu, c[[i, mu, 1]] < t[[mu]] < c[[i, mu, 2]]]]
        ],
        0
      ]
    },
    If[hit === 0,
      LoopBase,
      {gs}[[hit]][
        Table[
          (t[[mu]] - c[[hit, mu, 1]]) / (c[[hit, mu, 2]] - c[[hit, mu, 1]]),
          {mu, 1, Length[t]}
        ]
      ]
    ]
  ];

ApproximationMap[c_List, xs_List] := LoopAction[c] @@ Map[SuspensionUnit, xs];

(* from the last cube to the first, so that the positions of the cubes not
   yet used do not change *)
LittleCubesComposeAll[c_List, ds_List] :=
  Fold[
    Function[{acc, i}, LittleCubesCompose[acc, i, ds[[i]]]],
    c,
    Reverse[Range[Length[ds]]]
  ];

(* the midpoint of every cell, and the midpoint moved a quarter of the cell
   along each axis *)
LoopSamplePoints[c_List] :=
  With[{n = Length[First[c]]},
    With[{
        axes = Table[
          Partition[Union[{0, 1}, Flatten[c[[All, mu]]]], 2, 1],
          {mu, 1, n}
        ]
      },
      Flatten[
        Map[
          Function[cell,
            With[{mid = Map[Mean, cell]},
              Join[
                {mid},
                Table[
                  ReplacePart[mid, mu -> mid[[mu]] + (cell[[mu, 2]] - cell[[mu, 1]]) / 4],
                  {mu, 1, n}
                ]
              ]
            ]
          ],
          Tuples[axes]
        ],
        1
      ]
    ]
  ];

LoopEqualQ[g_, h_, c_List] :=
  AllTrue[LoopSamplePoints[c], Function[t, g[t] === h[t]]];

(* the centre goes around the square with the corners (1/4, 1/4), (3/4, 3/4),
   starting from (1/4, 1/2); the length of the way round is 2 *)
squarePoint[l0_] :=
  With[{l = Mod[l0, 2]},
    Which[
      l <= 1/4, {1/4, 1/2 - l},
      l <= 3/4, {1/4 + (l - 1/4), 1/4},
      l <= 5/4, {3/4, 1/4 + (l - 3/4)},
      l <= 7/4, {3/4 - (l - 5/4), 3/4},
      True, {1/4, 3/4 - (l - 7/4)}
    ]
  ];

swapCube[n_Integer, centre_List] :=
  Join[
    Map[Function[x, {x - 1/8, x + 1/8}], centre],
    ConstantArray[{0, 1}, n - 2]
  ];

SwapPath[n_Integer /; n >= 2][s_] :=
  {swapCube[n, squarePoint[s]], swapCube[n, squarePoint[s + 1]]};

End[];

EndPackage[];
