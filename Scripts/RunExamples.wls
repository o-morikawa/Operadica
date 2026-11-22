#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Evaluate the input cells of the notebooks in Examples/ in a plain kernel,
   in order, and report the cells that produce messages.

     wolframscript -file Scripts/RunExamples.wls                   all notebooks
     wolframscript -file Scripts/RunExamples.wls Operadica-Tour    only that one

   This checks that the code of the notebooks runs against the current
   package.  It is not a rendering: graphics and Manipulate are constructed
   but not displayed, and a cell that calls NotebookDirectory (the cell that
   loads the package from the notebook's folder) is skipped, since the package
   is loaded here.  The exit code is 0 if no cell produces a message and 1
   otherwise. *)

scriptFile = Which[
  StringQ[$InputFileName] && $InputFileName =!= "", $InputFileName,
  ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0, First[$ScriptCommandLine],
  True, FileNameJoin[{Directory[], "Scripts", "RunExamples.wls"}]
];
root = DirectoryName[ExpandFileName[scriptFile], 2];

selected = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 1,
  Rest[$ScriptCommandLine],
  {}
];

Print["Operadica root:   ", root];
Print["Wolfram Language: ", $Version];

PacletDirectoryLoad[root];
Needs["Operadica`"];
If[! MemberQ[$Packages, "Operadica`"],
  Get[FileNameJoin[{root, "Kernel", "Operadica.wl"}]]
];
If[! MemberQ[$Packages, "Operadica`"],
  Print["FATAL: the package did not load."];
  Exit[2]
];

(* the input cells of a notebook file, as strings *)
inputCells[file_String] :=
  Cases[Get[file], Cell[code_String, "Input", ___] :> code, Infinity];

(* evaluate the expressions of one cell, one after the other.  The result is
   {status, messages, seconds}; status is "ok", "skipped", "messages",
   "syntax" or "timeout".  VerificationTest records the messages *)
runCell[code_String] :=
  If[StringContainsQ[code, "NotebookDirectory"],
    {"skipped", {}, 0.},
    Module[{stream = StringToStream[code], expr, status = "ok", test, time},
      {time, test} = AbsoluteTiming[
        VerificationTest[
          TimeConstrained[
            While[
              status === "ok" && (expr = Read[stream, Hold[Expression]]) =!= EndOfFile,
              If[Head[expr] === Hold, ReleaseHold[expr], status = "syntax"]
            ],
            300,
            status = "timeout"
          ];
          status,
          "ok"
        ]
      ];
      Close[stream];
      {
        Which[
          status =!= "ok", status,
          Quiet[test["Outcome"]] === "Success", "ok",
          True, "messages"
        ],
        Quiet[test["ActualMessages"]],
        time
      }
    ]
  ];

files = Sort[FileNames["*.nb", FileNameJoin[{root, "Examples"}]]];
If[selected =!= {},
  files = Select[files, Function[f, MemberQ[selected, FileBaseName[f]]]]
];

allPassed = files =!= {};

Do[
  Module[{cells = inputCells[file], results, bad, time},
    results = Map[runCell, cells];
    bad = Select[Range[Length[cells]], Function[i, ! MemberQ[{"ok", "skipped"}, results[[i, 1]]]]];
    time = Total[results[[All, 3]]];
    Print[
      StringPadRight[FileNameTake[file], 24],
      Count[results[[All, 1]], "ok"], "/", Length[cells], " cells ok, ",
      Count[results[[All, 1]], "skipped"], " skipped   (",
      ToString[NumberForm[N[Round[10 time] / 10], {8, 1}]], " s)"
    ];
    If[Length[cells] === 0 || bad =!= {}, allPassed = False];
    Scan[
      Function[i,
        Print["  FAILED  input cell ", i, " (", results[[i, 1]], ")"];
        Print["    code:     ", StringTake[StringReplace[cells[[i]], "\n" -> " "], UpTo[160]]];
        Print["    messages: ", results[[i, 2]]]
      ],
      bad
    ]
  ],
  {file, files}
];

Print[If[allPassed, "ALL EXAMPLES RAN", "SOME EXAMPLES FAILED"]];
Exit[If[allPassed, 0, 1]];
