(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica`EnCategories`                                                *)
(*                                                                        *)
(*  Pointed E_n-monoidal categories: the simple objects are the elements   *)
(*  of a finite abelian group G = Z_N1 x ... x Z_Nr and the tensor product *)
(*  is the group law.  For ordinary categories                            *)
(*      E_1 = monoidal,   E_2 = braided,   E_n (n >= 3) = symmetric.       *)
(*                                                                        *)
(*  Data.  Phases are rational numbers modulo 1: x stands for exp(2 pi i x). *)
(*      associator  w[a, b, c]      (the F-symbol)                        *)
(*      braiding    c[a, b]         (the R-symbol)                        *)
(*  Group elements are lists of integers, {a1, ..., ar}.                   *)
(*                                                                        *)
(*  Conventions (abelian 3-cocycles of Eilenberg-MacLane, in the form of   *)
(*  Joyal-Street; checked in reference/encategory_reference.py):          *)
(*                                                                        *)
(*   pentagon   w(b,c,d) - w(a+b,c,d) + w(a,b+c,d) - w(a,b,c+d) + w(a,b,c) = 0 *)
(*   hexagon 1  w(b,c,a) + c(a,b+c) + w(a,b,c) = c(a,c) + w(b,a,c) + c(a,b) *)
(*   hexagon 2  -w(c,a,b) + c(a+b,c) - w(a,b,c) = c(a,c) - w(a,c,b) + c(b,c) *)
(*   symmetric  c(a,b) + c(b,a) = 0                                       *)
(*                                                                        *)
(*   gauge transformation by f[a, b]:                                     *)
(*       w' = w + df,  c'(a,b) = c(a,b) + f(b,a) - f(a,b),                *)
(*       (df)(a,b,c) = f(b,c) - f(a+b,c) + f(a,b+c) - f(a,b)              *)
(*                                                                        *)
(*   invariants: spin q(a) = c(a,a), mutual braiding b(a,b) = c(a,b) + c(b,a), *)
(*       q(a+b) - q(a) - q(b) = b(a,b).                                   *)
(*                                                                        *)
(*  Layer: category.  Depends on: nothing.                                *)
(* ====================================================================== *)

BeginPackage["Operadica`EnCategories`"];

PointedCategory::usage = "PointedCategory[{N1, ..., Nr}, w] gives the pointed monoidal category on the group Z_N1 x ... x Z_Nr with associator w[a, b, c]. PointedCategory[{N1, ..., Nr}, w, c] adds the braiding c[a, b]. Group elements are lists of integers and phases are rational numbers modulo 1. The result is an Association with the keys \"Name\", \"Group\", \"Associator\" and \"Braiding\".";

CategoryObjects::usage = "CategoryObjects[cat] lists the simple objects of the pointed category cat, the elements of its group.";

CategoryTensor::usage = "CategoryTensor[cat, a, b] gives the tensor product of the simple objects a and b, their sum in the group.";

PentagonQ::usage = "PentagonQ[cat] gives True if the associator of cat satisfies the pentagon equation, that is, if it is a 3-cocycle.";

HexagonQ::usage = "HexagonQ[cat] gives True if the associator and the braiding of cat satisfy both hexagon equations.";

SymmetricBraidingQ::usage = "SymmetricBraidingQ[cat] gives True if the double braiding c(a, b) + c(b, a) of cat is trivial for all objects.";

EnLevel::usage = "EnLevel[cat] gives 0 if cat is not monoidal (the pentagon fails), 1 if it is monoidal but not braided, 2 if it is braided but not symmetric, and Infinity if it is symmetric. For ordinary categories E_3 already means symmetric.";

TopologicalSpin::usage = "TopologicalSpin[cat, a] gives the spin c(a, a) of the object a, modulo 1.";

MutualBraiding::usage = "MutualBraiding[cat, a, b] gives the double braiding c(a, b) + c(b, a) of the objects a and b, modulo 1.";

SpinTable::usage = "SpinTable[cat] gives the Association from the objects of cat to their spins: the quadratic form of the braided category.";

MugerCenter::usage = "MugerCenter[cat] lists the objects of cat whose double braiding with every object is trivial. It is computed from the braiding data alone and does not check the pentagon and hexagon equations.";

ModularQ::usage = "ModularQ[cat] gives True if cat is a braided category (the pentagon and hexagon equations hold) whose Mueger center consists of the unit object only. For data that are not a braided category it gives False.";

BraidPhase::usage = "BraidPhase[cat, word, i] gives the phase, modulo 1, of the braid generator sigma_i that exchanges the i-th and (i+1)-th objects of the right-nested product of the objects in word: for the last two objects it is the braiding c(a, b), and otherwise -w(a, b, x) + c(a, b) + w(b, a, x) with x the product of the objects that follow.";

BraidWord::usage = "BraidWord[word, i] gives the word with its i-th and (i+1)-th objects exchanged.";

BraidRelationQ::usage = "BraidRelationQ[cat, n] gives True if the phases of the braid generators satisfy sigma_i sigma_(i+1) sigma_i = sigma_(i+1) sigma_i sigma_(i+1) on all products of n objects. For a pointed category this follows from the pentagon equation; the hexagon equations are the statements that braiding past a product is the composite of the braidings.";

GaugeTransformCategory::usage = "GaugeTransformCategory[cat, f] gives the category obtained from cat by the gauge transformation with the 2-cochain f[a, b]: w' = w + df and c'(a, b) = c(a, b) + f(b, a) - f(a, b). It is equivalent to cat.";

ZNAnyons::usage = "ZNAnyons[n, p] gives the braided category Z_n^(p): associator w(a, b, c) = p a carry(b, c) / 2 and braiding c(a, b) = p a b / (2 n), with carry(b, c) = 1 if b + c >= n and 0 otherwise. It satisfies the axioms when n is even or p is even; the spin of a is p a^2 / (2 n).";

VecZN::usage = "VecZN[n, k] gives the monoidal category of Z_n-graded vector spaces with associator w(a, b, c) = k a carry(b, c) / n, a representative of the class k in H^3(Z_n, U(1)) = Z_n. It has no braiding.";

DoubleZN::usage = "DoubleZN[n] gives the braided category of Z_n gauge theory in 2+1 dimensions, on the group Z_n x Z_n with objects {e, m}: trivial associator and braiding c({e1, m1}, {e2, m2}) = e1 m2 / n.";

ToricCode::usage = "ToricCode[] gives DoubleZN[2]: the objects {1, 0} and {0, 1} are bosons with mutual braiding 1/2, and {1, 1} is a fermion.";

Semion::usage = "Semion[] gives ZNAnyons[2, 1], whose nontrivial object has spin 1/4.";

SuperVec::usage = "SuperVec[] gives ZNAnyons[2, 2], the symmetric category of super vector spaces: the nontrivial object is a fermion, with spin 1/2.";

Begin["`Private`"];

(* ---------------------------------------------------------------------- *)
(* the group                                                              *)
(* ---------------------------------------------------------------------- *)

elements[orders_List] := Tuples[Map[Function[n, Range[0, n - 1]], orders]];

add[orders_List][a_List, b_List] := Mod[a + b, orders];

phaseZeroQ[x_] := Mod[x, 1] === 0;


PointedCategory[orders : {__Integer}, w_] := PointedCategory[orders, w, None];

PointedCategory[orders : {__Integer}, w_, c_] :=
  <|
    "Name" -> "Pointed",
    "Group" -> orders,
    "Associator" -> w,
    "Braiding" -> c
  |>;

CategoryObjects[cat_Association] := elements[cat["Group"]];

CategoryTensor[cat_Association, a_List, b_List] := add[cat["Group"]][a, b];


(* ---------------------------------------------------------------------- *)
(* axioms                                                                 *)
(* ---------------------------------------------------------------------- *)

PentagonQ[cat_Association] :=
  With[{w = cat["Associator"], plus = add[cat["Group"]], els = elements[cat["Group"]]},
    AllTrue[
      Tuples[els, 4],
      Function[t,
        With[{g1 = t[[1]], g2 = t[[2]], g3 = t[[3]], g4 = t[[4]]},
          phaseZeroQ[
            w[g2, g3, g4] - w[plus[g1, g2], g3, g4] + w[g1, plus[g2, g3], g4] -
              w[g1, g2, plus[g3, g4]] + w[g1, g2, g3]
          ]
        ]
      ]
    ]
  ];


HexagonQ[cat_Association] :=
  With[{w = cat["Associator"], br = Lookup[cat, "Braiding", None],
      plus = add[cat["Group"]], els = elements[cat["Group"]]},
    br =!= None &&
      AllTrue[
        Tuples[els, 3],
        Function[t,
          With[{g1 = t[[1]], g2 = t[[2]], g3 = t[[3]]},
            phaseZeroQ[
              (w[g2, g3, g1] + br[g1, plus[g2, g3]] + w[g1, g2, g3]) -
                (br[g1, g3] + w[g2, g1, g3] + br[g1, g2])
            ] &&
            phaseZeroQ[
              (-w[g3, g1, g2] + br[plus[g1, g2], g3] - w[g1, g2, g3]) -
                (br[g1, g3] - w[g1, g3, g2] + br[g2, g3])
            ]
          ]
        ]
      ]
  ];


SymmetricBraidingQ[cat_Association] :=
  With[{br = Lookup[cat, "Braiding", None], els = elements[cat["Group"]]},
    br =!= None &&
      AllTrue[Tuples[els, 2], Function[t, phaseZeroQ[br[t[[1]], t[[2]]] + br[t[[2]], t[[1]]]]]]
  ];


EnLevel[cat_Association] :=
  Which[
    ! PentagonQ[cat], 0,
    ! HexagonQ[cat], 1,
    ! SymmetricBraidingQ[cat], 2,
    True, Infinity
  ];


(* ---------------------------------------------------------------------- *)
(* invariants                                                             *)
(* ---------------------------------------------------------------------- *)

TopologicalSpin[cat_Association, a_List] := Mod[cat["Braiding"][a, a], 1];

MutualBraiding[cat_Association, a_List, b_List] :=
  Mod[cat["Braiding"][a, b] + cat["Braiding"][b, a], 1];

SpinTable[cat_Association] :=
  Association[Map[Function[a, a -> TopologicalSpin[cat, a]], CategoryObjects[cat]]];

MugerCenter[cat_Association] :=
  With[{els = CategoryObjects[cat]},
    Select[els, Function[a, AllTrue[els, Function[b, MutualBraiding[cat, a, b] === 0]]]]
  ];

(* the double braiding of data that fail the hexagons can be non-degenerate
   without there being any braided category *)
ModularQ[cat_Association] :=
  PentagonQ[cat] && HexagonQ[cat] && Length[MugerCenter[cat]] === 1;


(* ---------------------------------------------------------------------- *)
(* the braid groups                                                       *)
(*   the product of a word is nested to the right: a1 (a2 (a3 ...))       *)
(*   sigma_i:  a (b X) -> (a b) X -> (b a) X -> b (a X)                   *)
(* ---------------------------------------------------------------------- *)

BraidWord[word_List, i_Integer] :=
  ReplacePart[word, {i -> word[[i + 1]], i + 1 -> word[[i]]}];

BraidPhase[cat_Association, word_List, i_Integer] /; 1 <= i < Length[word] :=
  With[{w = cat["Associator"], br = cat["Braiding"], g1 = word[[i]], g2 = word[[i + 1]]},
    If[i === Length[word] - 1,
      Mod[br[g1, g2], 1],
      With[{tail = Mod[Total[Drop[word, i + 1]], cat["Group"]]},
        Mod[-w[g1, g2, tail] + br[g1, g2] + w[g2, g1, tail], 1]
      ]
    ]
  ];

braidPathPhase[cat_Association, word_List, {}] := 0;

braidPathPhase[cat_Association, word_List, {i_Integer, rest___}] :=
  BraidPhase[cat, word, i] + braidPathPhase[cat, BraidWord[word, i], {rest}];

BraidRelationQ[cat_Association, n_Integer /; n >= 3] :=
  AllTrue[
    Tuples[CategoryObjects[cat], n],
    Function[word,
      AllTrue[
        Range[n - 2],
        Function[i,
          Mod[
            braidPathPhase[cat, word, {i, i + 1, i}] - braidPathPhase[cat, word, {i + 1, i, i + 1}],
            1
          ] === 0
        ]
      ]
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* gauge transformations                                                  *)
(* ---------------------------------------------------------------------- *)

GaugeTransformCategory[cat_Association, f_] :=
  With[{w = cat["Associator"], br = Lookup[cat, "Braiding", None], plus = add[cat["Group"]]},
    Join[
      cat,
      <|
        "Associator" -> Function[{h1, h2, h3},
          w[h1, h2, h3] + f[h2, h3] - f[plus[h1, h2], h3] + f[h1, plus[h2, h3]] - f[h1, h2]
        ],
        "Braiding" -> If[br === None, None, Function[{h1, h2}, br[h1, h2] + f[h2, h1] - f[h1, h2]]]
      |>
    ]
  ];


(* ---------------------------------------------------------------------- *)
(* examples                                                               *)
(* ---------------------------------------------------------------------- *)

(* for representatives 0 <= b, c < n : 1 if b + c >= n, else 0 *)
carry[n_Integer, b_Integer, c_Integer] := Quotient[Mod[b, n] + Mod[c, n], n];

ZNAnyons[n_Integer?Positive, p_Integer] :=
  Join[
    PointedCategory[{n},
      Function[{x, y, z}, p Mod[x[[1]], n] carry[n, y[[1]], z[[1]]] / 2],
      Function[{x, y}, p Mod[x[[1]], n] Mod[y[[1]], n] / (2 n)]
    ],
    <|"Name" -> "Z" <> ToString[n] <> "^(" <> ToString[p] <> ")"|>
  ];

VecZN[n_Integer?Positive, k_Integer] :=
  Join[
    PointedCategory[{n},
      Function[{x, y, z}, k Mod[x[[1]], n] carry[n, y[[1]], z[[1]]] / n]
    ],
    <|"Name" -> "Vec_Z" <> ToString[n] <> "^" <> ToString[k]|>
  ];

DoubleZN[n_Integer?Positive] :=
  Join[
    PointedCategory[{n, n},
      Function[{x, y, z}, 0],
      Function[{x, y}, Mod[x[[1]], n] Mod[y[[2]], n] / n]
    ],
    <|"Name" -> "D(Z" <> ToString[n] <> ")"|>
  ];

ToricCode[] := DoubleZN[2];

Semion[] := ZNAnyons[2, 1];

SuperVec[] := ZNAnyons[2, 2];

End[];

EndPackage[];
