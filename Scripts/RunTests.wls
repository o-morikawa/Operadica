#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Run every test file in Tests/ and report failures.

     wolframscript -file Scripts/RunTests.wls              all test files
     wolframscript -file Scripts/RunTests.wls Lattice      only Tests/Lattice.wlt

   The exit code is 0 if all tests pass and 1 otherwise. *)

scriptFile = Which[
  StringQ[$InputFileName] && $InputFileName =!= "", $InputFileName,
  ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0, First[$ScriptCommandLine],
  True, FileNameJoin[{Directory[], "Scripts", "RunTests.wls"}]
];

root = DirectoryName[ExpandFileName[scriptFile], 2];

selected = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
  Rest[$ScriptCommandLine],
  {}
];

Print["Operadica root:   ", root];
Print["Wolfram Language: ", $Version];

PacletDirectoryLoad[root];

allPassed = True;

(* 1. a single layer loads on its own, without the operad layer *)
layerLoaded = Check[Needs["Operadica`Lattice`"]; True, False];
layerOK = TrueQ[layerLoaded] &&
  MemberQ[$Packages, "Operadica`Lattice`"] &&
  ! MemberQ[$Packages, "Operadica`Trees`"];
Print["single layer (Operadica`Lattice`) loads alone: ", If[layerOK, "ok", "FAILED"]];
If[! layerOK, allPassed = False];

(* 2. everything *)
Needs["Operadica`"];

If[! MemberQ[$Packages, "Operadica`"],
  Print["Needs could not load the paclet; reading Kernel/Operadica.wl directly."];
  Get[FileNameJoin[{root, "Kernel", "Operadica.wl"}]]
];

If[! MemberQ[$Packages, "Operadica`"],
  Print["FATAL: the package did not load."];
  Exit[2]
];

missing = Select[Operadica`$OperadicaLayers, Function[ctx, ! MemberQ[$Packages, ctx]]];
Print["layers loaded: ", Length[Operadica`$OperadicaLayers] - Length[missing], "/", Length[Operadica`$OperadicaLayers],
  If[missing === {}, "", "   missing: " <> ToString[missing]]];
If[missing =!= {}, allPassed = False];

(* TestReportObject changed its property names in version 13.3; read the
   results in a way that works before and after. *)
getResults[report_] :=
  Module[{r},
    r = Quiet[report["TestResults"]];
    If[AssociationQ[r], r = Values[r]];
    If[! ListQ[r],
      r = Quiet[report["Results"]];
      If[AssociationQ[r], r = Values[r]]
    ];
    If[ListQ[r], r, {}]
  ];

outcomeOf[t_] := Quiet[t["Outcome"]];

testFiles = Sort[FileNames["*.wlt", FileNameJoin[{root, "Tests"}]]];
If[selected =!= {},
  testFiles = Select[testFiles, Function[f, MemberQ[selected, FileBaseName[f]]]]
];

totalRun = 0;
totalOK = 0;

Do[
  Module[{report, results, bad, time},
    {time, report} = AbsoluteTiming[TestReport[file]];
    results = getResults[report];
    bad = Select[results, outcomeOf[#] =!= "Success" &];
    totalRun = totalRun + Length[results];
    totalOK = totalOK + Length[results] - Length[bad];
    Print[
      StringPadRight[FileNameTake[file], 20],
      Length[results] - Length[bad], "/", Length[results], " passed   (",
      Round[time, 0.1], " s)"
    ];
    If[Length[results] === 0 || Length[bad] > 0, allPassed = False];
    Scan[
      Function[t,
        Print["  FAILED   ", Quiet[t["TestID"]], "   [", outcomeOf[t], "]"];
        Print["    actual:   ", Short[Quiet[t["ActualOutput"]], 4]];
        Print["    expected: ", Short[Quiet[t["ExpectedOutput"]], 4]];
        Print["    messages: ", Short[Quiet[t["ActualMessages"]], 4]]
      ],
      bad
    ]
  ],
  {file, testFiles}
];

Print[""];
Print[totalOK, "/", totalRun, " tests passed."];
Print[If[allPassed, "ALL TESTS PASSED", "SOME TESTS FAILED"]];

Exit[If[allPassed, 0, 1]];
