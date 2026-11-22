(* ::Package:: *)

(* ====================================================================== *)
(*  Operadica -- operads, E_n categories and lattice cochains, computed    *)
(*                                                                        *)
(*  Load everything:                                                      *)
(*      PacletDirectoryLoad["/path/to/Operadica"];                        *)
(*      Needs["Operadica`"]                                               *)
(*                                                                        *)
(*  or one layer at a time (its dependencies are loaded automatically):   *)
(*                                                                        *)
(*    operad layer                                                        *)
(*      Operadica`Trees`         planar trees, grafting                   *)
(*      Operadica`Operads`       operad objects, axiom and equivariance   *)
(*                               verifiers, algebras                      *)
(*      Operadica`Rewriting`     quotient operads, confluence             *)
(*      Operadica`LittleCubes`   the little n-cubes operads E_n           *)
(*      Operadica`Graded`        graded and differential graded operads   *)
(*      Operadica`AInfinity`     the A-infinity operad, associahedra      *)
(*      Operadica`Presented`     symmetric operads by generators and      *)
(*                               relations: Com, Lie, Ass, Poisson,       *)
(*                               Gerstenhaber, P_n                        *)
(*      Operadica`BarrattEccles` the Barratt-Eccles operad (E-infinity),  *)
(*                               its E_n stages, its action on cubes      *)
(*      Operadica`BarConstruction` delooping: the iterated bar          *)
(*                               construction of an abelian group, and    *)
(*                               the Eilenberg-MacLane spaces K(A, n)     *)
(*    category layer                                                      *)
(*      Operadica`EnCategories`  pointed E_n-monoidal categories          *)
(*    lattice gauge theory layer                                          *)
(*      Operadica`Lattice`       cochains, coboundary, cup, higher cup    *)
(*      Operadica`Gauge`         expansion, gauge variations, actions     *)
(*      Operadica`Simplicial`    the same cochain expressions on simplices: *)
(*                               Steenrod's cup-i products                *)
(*    bridge                                                              *)
(*      Operadica`EInfinity`     the E-infinity operad acts on lattice    *)
(*                               cochains: higher cup products and the    *)
(*                               homotopies between them                  *)
(*      Operadica`Bridge`        statements connecting the layers         *)
(* ====================================================================== *)

(* Read the layers from the files next to this one, in dependency order.
   This makes Get on this file work without paclet resolution; with the
   paclet loaded, Needs on a layer context finds the same files. *)
With[{dir = DirectoryName[$InputFileName]},
  Scan[
    Function[name,
      If[! MemberQ[$Packages, "Operadica`" <> name <> "`"],
        Get[FileNameJoin[{dir, name <> ".wl"}]]
      ]
    ],
    {"Trees", "Operads", "Rewriting", "LittleCubes", "Graded", "AInfinity", "Presented", "BarrattEccles", "BarConstruction", "Lattice", "Gauge", "Simplicial", "EnCategories", "EInfinity", "Bridge"}
  ]
];

BeginPackage["Operadica`", {
  "Operadica`Trees`",
  "Operadica`Operads`",
  "Operadica`Rewriting`",
  "Operadica`LittleCubes`",
  "Operadica`Graded`",
  "Operadica`AInfinity`",
  "Operadica`Presented`",
  "Operadica`BarrattEccles`",
  "Operadica`BarConstruction`",
  "Operadica`Lattice`",
  "Operadica`Gauge`",
  "Operadica`Simplicial`",
  "Operadica`EnCategories`",
  "Operadica`EInfinity`",
  "Operadica`Bridge`"
}];

$OperadicaLayers::usage = "$OperadicaLayers lists the contexts of the layers of Operadica, in dependency order.";

Begin["`Private`"];

$OperadicaLayers = {
  "Operadica`Trees`",
  "Operadica`Operads`",
  "Operadica`Rewriting`",
  "Operadica`LittleCubes`",
  "Operadica`Graded`",
  "Operadica`AInfinity`",
  "Operadica`Presented`",
  "Operadica`BarrattEccles`",
  "Operadica`BarConstruction`",
  "Operadica`Lattice`",
  "Operadica`Gauge`",
  "Operadica`Simplicial`",
  "Operadica`EnCategories`",
  "Operadica`EInfinity`",
  "Operadica`Bridge`"
};

End[];

EndPackage[];
