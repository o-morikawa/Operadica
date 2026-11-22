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
(*  Paths of configurations and their braids.  A path of configurations   *)
(*  of k little n-cubes (n >= 2) is read in the first two directions: the  *)
(*  cubes are ordered by their centres, lexicographically in (x, y), and   *)
(*  when two neighbours change places between two samples of the path the  *)
(*  relative position of the right one turns either counterclockwise (the  *)
(*  cube from the left passes below: the generator sigma_i) or clockwise   *)
(*  (its inverse).  PathBraid gives the braid as a list of integers, +i    *)
(*  for sigma_i and -i for its inverse.  For n = 2 the braid is the        *)
(*  homotopy class of the path; for n >= 3 it is not an invariant, and     *)
(*  SwapHomotopy is a homotopy between the two half turns.                 *)
(*                                                                        *)
(*  Checked in reference/loops_reference.py and                           *)
(*  reference/braiding_reference.py.                                      *)
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

ConfigurationOrder::usage = "ConfigurationOrder[c] gives the labels of the cubes of the configuration c of little n-cubes (n >= 2) from left to right: ordered by the first coordinate of the centre, and by the second coordinate when the first ones agree. It gives $Failed if two centres agree in the first two coordinates.";

PathBraid::usage = "PathBraid[path, {s0, s1}, steps] gives the braid of the path s -> path[s] of configurations of little n-cubes (n >= 2), read in the first two directions and sampled at steps + 1 equally spaced values from s0 to s1. The braid is a list of nonzero integers: i stands for the generator sigma_i, the counterclockwise exchange of the cubes at the positions i and i + 1 from the left (the cube from the left passes below), and -i for its inverse. Between two samples every relative position must turn by less than a half turn, and only neighbours may change places; otherwise, or if two centres coincide in the plane, the result is $Failed and more steps are needed. For n = 2 the braid is the homotopy class of the path.";

ExchangeCount::usage = "ExchangeCount[path, {s0, s1}, steps] gives the exponent sum of PathBraid[path, {s0, s1}, steps]. For two cubes it is the number of counterclockwise half turns of the cubes around each other.";

SwapHomotopy::usage = "SwapHomotopy[u][s] gives, for 0 <= u <= 1 and 0 <= s <= 1, a configuration of two little 3-cubes. For u = 0 the path in s is the counterclockwise half turn SwapPath[2] in the first two directions, for u = 1 its mirror image, the clockwise half turn, and the configurations at s = 0 and s = 1 do not depend on u: a homotopy between the two ways to exchange two cubes, which exists in three dimensions and not in two.";

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


(* ---------------------------------------------------------------------- *)
(* the braid of a path of configurations                                  *)
(* ---------------------------------------------------------------------- *)

planeCentre[cube_List] := {Mean[cube[[1]]], Mean[cube[[2]]]};

ConfigurationOrder[c_List] :=
  With[{pts = Map[planeCentre, c]},
    If[DuplicateFreeQ[pts],
      SortBy[Range[Length[c]], {Function[lab, pts[[lab, 1]]], Function[lab, pts[[lab, 2]]]}],
      $Failed
    ]
  ];

(* the generators between two consecutive samples: the positions are read
   from the left; two neighbours p, q that change places give the sign of
   the cross product of the relative positions before and after *)
stepGenerators[prev_List, cur_List, oprev_List, ocur_List, pos_Integer] :=
  Which[
    pos > Length[oprev],
      {},
    oprev[[pos]] === ocur[[pos]],
      stepGenerators[prev, cur, oprev, ocur, pos + 1],
    pos < Length[oprev] && oprev[[pos]] === ocur[[pos + 1]] && oprev[[pos + 1]] === ocur[[pos]],
      With[{
          r0 = planeCentre[prev[[oprev[[pos + 1]]]]] - planeCentre[prev[[oprev[[pos]]]]],
          r1 = planeCentre[cur[[oprev[[pos + 1]]]]] - planeCentre[cur[[oprev[[pos]]]]],
          rest = stepGenerators[prev, cur, oprev, ocur, pos + 2]
        },
        With[{z = r0[[1]] r1[[2]] - r0[[2]] r1[[1]]},
          If[z == 0 || rest === $Failed, $Failed, Prepend[rest, Sign[z] pos]]
        ]
      ],
    True,
      $Failed
  ];

braidStep[prev_List, cur_List] :=
  With[{oprev = ConfigurationOrder[prev], ocur = ConfigurationOrder[cur]},
    If[oprev === $Failed || ocur === $Failed,
      $Failed,
      stepGenerators[prev, cur, oprev, ocur, 1]
    ]
  ];

PathBraid[path_, {s0_, s1_}, steps_Integer?Positive] :=
  With[{configs = Table[path[s0 + (s1 - s0) j / steps], {j, 0, steps}]},
    With[{parts = Table[braidStep[configs[[j]], configs[[j + 1]]], {j, 1, steps}]},
      If[MemberQ[parts, $Failed], $Failed, Join @@ parts]
    ]
  ];

ExchangeCount[path_, {s0_, s1_}, steps_Integer?Positive] :=
  With[{braid = PathBraid[path, {s0, s1}, steps]},
    If[braid === $Failed, $Failed, Total[Sign[braid]]]
  ];


(* ---------------------------------------------------------------------- *)
(* three dimensions: the two half turns are homotopic                     *)
(*   the plane of the half turn is spanned by the first direction and by   *)
(*   a vector v(u) that goes from the second direction, through the third, *)
(*   to minus the second; v(u) stays on the square max(|v2|, |v3|) = 1, so *)
(*   that the two cubes of side 1/4 stay 1/2 apart                         *)
(* ---------------------------------------------------------------------- *)

homotopyDirection[u_] :=
  Which[
    u <= 1/4, {1, 4 u},
    u <= 3/4, {2 - 4 u, 1},
    True, {-1, 4 - 4 u}
  ];

homotopyCube[q_List, v_List] :=
  Map[
    Function[x, {x - 1/8, x + 1/8}],
    {q[[1]], 1/2 + (q[[2]] - 1/2) v[[1]], 1/2 + (q[[2]] - 1/2) v[[2]]}
  ];

SwapHomotopy[u_][s_] :=
  With[{v = homotopyDirection[u]},
    {homotopyCube[squarePoint[s], v], homotopyCube[squarePoint[s + 1], v]}
  ];

End[];

EndPackage[];
