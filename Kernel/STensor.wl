(* ::Package:: *)

BeginPackage["BowenPing`STensor`"]


Private`syms =
{
	STensor,
	CreateTensor,
	STensorQ,
	ChristoffelSymbol,
	RiemannTensor,
	RicciTensor,
	RicciScalar,
	EinsteinTensor,
	WeylTensor,
	IsMetric,
	Symmetry
}
Unprotect @@ Private`syms


STensor::usage = "STensor is an integrated tensor object.";


STensorQ::usage = "STensorQ[expr] tests if expr is a STensor object.";


CreateTensor::usage = "CreateTensor[\!\(\*StyleBox[\"Sym\",\nFontSlant->\"Italic\"]\), \!\(\*StyleBox[\"Rank\",\nFontSlant->\"Italic\"]\), \!\(\*StyleBox[\"CoorS\",\nFontSlant->\"Italic\"]\), \!\(\*StyleBox[\"Comp\",\nFontSlant->\"Italic\"]\), \!\(\*StyleBox[\"Metric\",\nFontSlant->\"Italic\"]\)]"<>" "<>"creates a STensor object with symbol \!\(\*StyleBox[\"Sym\",\nFontSlant->\"Italic\"]\), rank \!\(\*StyleBox[\"Rank\",\nFontSlant->\"Italic\"]\), Coordinate System \!\(\*StyleBox[\"CoorS\",\nFontSlant->\"Italic\"]\), Components \!\(\*StyleBox[\"Comp\",\nFontSlant->\"Italic\"]\) and metric \!\(\*StyleBox[\"Metric\",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\".\",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\"Sym\",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\" \",\nFontSlant->\"Italic\"]\)and\!\(\*StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\"Rank\",\nFontSlant->\"Italic\"]\)\!\(\*StyleBox[\" \",\nFontSlant->\"Italic\"]\)are neccesary.";


ChristoffelSymbol::usage = "ChristoffelSymbol[metric] returns its Christoffel symbol.";
RiemannTensor::usage = "RiemannTensor[metric] returns its Riemann Tensor.";
RicciTensor::usage = "RicciTensor[metric] returns its Ricci Tensor.";
RicciScalar::usage = "RicciScalar[metric] returns its Ricci scalar.";
EinsteinTensor::usage = "EinsteinTensor[metric] returns its Einstein Tensor.";
WeylTensor::usage = "WeylTensor[metric] returns its Weyl Tensor.";
VolumeElement::usage = "VolumeElement[metric] returns its volume element.";
LineElement::usage = "LineElement[metric] returns its line element.";


IsMetric::usage = "IsMetric indicates if the STensor is a metric.";


SCoordinateTransform::usage =
"SCoordinateTransform[T, targetCods, Transformation, invTransformation] do coordinate transformation to targetCods on T.
SCoordinateTransform[T, targetCods, cod1 -> cod2] do coordinate transformation from cod1 to cod2."


Private`systemsyms = StringJoin["System`", #]& /@ {"Grad", "D", "TensorSymmetry", "TensorRank", "TensorDimensions", "TensorTranspose", "Symmetrize", "Simplify", "FullSimplify", "Inverse", "Tr"};
Unprotect @@ (ToExpression /@ Private`systemsyms);


Begin["BowenPing`Private`"]


(* ::Section::Closed:: *)
(*Object Test*)


STensorAsQ[asc_?AssociationQ] :=
	AllTrue[{"Symbol", "Rank"}, KeyExistsQ[asc, #]&]

STensorAsQ[_] = False;

STensorQ[T : STensor[asc_]] :=
	STensorAsQ[asc];

STensorQ[_] = False;


(* ::Section::Closed:: *)
(*Formatting*)


(* ::Subsection::Closed:: *)
(*TraditionalForm*)


STensor::WrongIndicesnum = "Number of indices {`1`} does not match with the rank `2`."
STensor::WrongIndicesNum = "Number of indices {`1`, `2`} does not match with the rank `3`."


STensor /: MakeBoxes[tensor : STensor[T_?STensorAsQ][indices_String], form : TraditionalForm] :=
Module[
	{},
	Which[
		MatchQ[T["Rank"],{x_Integer/;x!=0, 0}], SubsuperscriptBox[StringJoin["(", T["Symbol"], ")"], "", indices],
		MatchQ[T["Rank"],{0, x_Integer/;x!=0}], SubsuperscriptBox[StringJoin["(", T["Symbol"], ")"], indices, ""],
		True, Message[STensor::WrongIndicesnum, indices, T["Rank"]]
	]
];


STensor /: MakeBoxes[tensor : STensor[T_?STensorAsQ][indices : PatternSequence[sup_String, sub_String]], form : TraditionalForm] :=
Module[
	{},
	If[
		StringLength /@ {indices} == T["Rank"],
		SubsuperscriptBox[StringJoin["(", T["Symbol"], ")"], sub, sup],
		Message[STensor::WrongIndicesNum, sup, sub, T["Rank"]]
	]
];


STensor /: MakeBoxes[tensor : STensor[T_?STensorAsQ], form : TraditionalForm] :=
Module[
	{
	sublen = T["Rank"][[2]],
	suplen = T["Rank"][[1]],
	scriptform
	},
	
	scriptform[s_Integer, e_Integer] := StyleBox[StringJoin[Alphabet[][[s ;; e]]], Italic];
	
	SubsuperscriptBox[StringJoin["(", T["Symbol"], ")"], scriptform[suplen + 1, sublen + suplen], scriptform[1, suplen]]
];


(* ::Subsection::Closed:: *)
(*StandardForm*)


STensor /: MakeBoxes[tensor : STensor[T_?STensorAsQ], form : StandardForm] :=
Module[{above, below, icon},
	above = {
		BoxForm`SummaryItem[{"Symbol: ", ToString[T["Symbol"]], SpanFromLeft}],
		BoxForm`SummaryItem[{"Rank: ", T["Rank"]}]
		};
	below = If[KeyExistsQ[T, #], BoxForm`SummaryItem[{StringJoin[#, ": "], T[#]}], Nothing]&
			/@ {"Symmetry", "Coordinate System", "Components", "Metric"};
	
	(*Make icon*)
	
	icon = ArrayPlot[ArrayReshape[(# @@ (T["Rank"] + 1))& /@ {Times, Plus, Subtract, Divide}, {2, 2}], ColorFunction -> Hue];
	
	BoxForm`ArrangeSummaryBox[STensor, tensor, icon, above, below, form, "Interpretable" -> Automatic]
];


(* ::Section::Closed:: *)
(*Create STensor Objects*)


Options[CreateTensor] = {IsMetric -> False, Symmetry -> {}};


STensor::MatchError = "`1`(`2`) and `3`(`4`) do not match.";
STensor::MetricError = "`` is not a metric.";


(* ::Subsection::Closed:: *)
(*IsMetric -> True*)


CreateTensor[sym_String : "g", opt: OptionsPattern[]]:=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> {0, 2},
		"Symmetry" -> {Symmetric[{1, 2}]},
		"Metric" -> True
		|>] /; OptionValue[IsMetric] === True;


CreateTensor[sym_String : "g", cods_List /; AllTrue[cods, Head[#] == Symbol&], opt: OptionsPattern[]]:=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> {0, 2},
		"Symmetry" -> {Symmetric[{1, 2}]},
		"Coordinate System" -> cods,
		"Metric" -> True
		|>] /; OptionValue[IsMetric] === True;


CreateTensor[sym_String : "g", cods_List /; AllTrue[cods, Head[#] === Symbol&], components_?ArrayQ, opt: OptionsPattern[]]:=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> {0, 2},
		"Symmetry" -> {Symmetric[{1, 2}]},
		"Coordinate System" -> cods,
		"Components" -> If[SymmetricMatrixQ[components], Identity, Symmetrize, Symmetrize][components],
		"Metric" -> True
		|>] /; OptionValue[IsMetric] === True;


CreateTensor[sym_String : "g", rank : {0,2}, cods_List /; AllTrue[cods, Head[#] === Symbol&], components_?ArrayQ, opt: OptionsPattern[]]:=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> {0, 2},
		"Symmetry" -> {Symmetric[{1, 2}]},
		"Coordinate System" -> cods,
		"Components" -> If[SymmetricMatrixQ[components], Identity, Symmetrize, Symmetrize][components],
		"Metric" -> True
		|>] /; OptionValue[IsMetric] === True;


(* ::Subsection::Closed:: *)
(*General Case*)


CreateTensor[sym_String, rank : {suplen_Integer, sublen_Integer}, opt: OptionsPattern[]] :=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> rank,
		"Symmetry" -> OptionValue[Symmetry],
		If[OptionValue[IsMetric], "Metric" -> True, Nothing]
		|>]


CreateTensor[sym_String, rank : {suplen_Integer, sublen_Integer}, cods_List /; AllTrue[cods, Head[#] == Symbol&], opt: OptionsPattern[]] :=
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> rank,
		"Symmetry" -> OptionValue[Symmetry],
		"Coordinate System" -> cods,
		If[OptionValue[IsMetric], "Metric" -> True, Nothing]
		|>]

CreateTensor[sym_String, rank : {suplen_Integer, sublen_Integer}, cods_List/; AllTrue[cods, Head[#] == Symbol&], components_?ArrayQ, opt: OptionsPattern[]] :=
Which[
	Length[cods] =!= First[TensorDimensions[components]], Message[STensor::MatchError, "Dimension of Coordiante System", Length[cods], "Dimension of Components", First[TensorDimensions[components]]];Abort[],
	Plus @@ rank =!= TensorRank[components], Message[STensor::MatchError, "Rank", rank, "rank of components", TensorRank[components]];Abort[],
	True,
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> rank,
		"Symmetry" -> OptionValue[Symmetry],
		"Coordinate System" -> cods,
		"Components" -> Symmetrize[components, OptionValue[Symmetry]],
		If[OptionValue[IsMetric], "Metric" -> True, Nothing]
	|>]
]

CreateTensor[sym_String, rank : {suplen_Integer, sublen_Integer}, cods_List/; AllTrue[cods, Head[#] == Symbol&], components_?ArrayQ, metric_?STensorQ, opt : OptionsPattern[]] :=
Which[
	Length[cods] =!= First[TensorDimensions[components]], Message[STensor::MatchError, "Dimension of Coordiante System", Length[cods], "Dimension of Components", First[TensorDimensions[components]]];Abort[],
	Plus @@ rank =!= TensorRank[components], Message[STensor::MatchError, "Rank", rank, "rank of components", TensorRank[components]];Abort[],
	cods =!= metric["Coordinate System"], Message[STensor::MatchError, "Coordinate System", cods, "Coordinate System of Metric", metric["Coordinate System"]];Abort[],
	(First[metric])["Metric"] =!= True, Message[STensor::MetricError, metric["Symbol"]];Abort[],
	True,
	STensor[<|
		"Symbol" -> sym,
		"Rank" -> rank,
		"Symmetry" -> OptionValue[Symmetry],
		"Coordinate System" -> cods,
		"Components" -> Symmetrize[components, OptionValue[Symmetry]],
		"Metric" -> metric
	|>]
]


CreateTensor[asc_?STensorAsQ] := STensor[asc]


CreateTensor[rules___Rule] := CreateTensor[Association[rules]]


(* ::Section::Closed:: *)
(*Get Values*)


(*metric's Metric*)

(*Without indices*)
STensor /: (metric_STensor)["Metric"] := metric /; STensorQ[metric] && First[metric]["Metric"] === True
(*With indices*)
STensor /: (metric_STensor)[indices:(_?LetterQ | PatternSequence[_?LetterQ, _?LetterQ])]["Metric"] := metric /; STensorQ[metric] && First[metric]["Metric"] === True


(*Without indices*)
STensor[asc_?STensorAsQ][comp_String] := asc[comp] /; KeyExistsQ[asc, comp]

(*With indices*)
STensor[asc_?STensorAsQ][indices:(_?LetterQ | PatternSequence[_?LetterQ, _?LetterQ])][comp_String] := asc[comp] /; KeyExistsQ[asc, comp]


(*Get Non-zero Components*)

(*Without indices*)
STensor[asc_?STensorAsQ /; SameQ[asc["Rank"], {0, 0}]]["Non-zero Components"] := If[asc["Components"] =!= 0, asc["Symbol"] -> asc["Components"], {}]

STensor[asc_?STensorAsQ /; UnsameQ[asc["Rank"], {0, 0}]]["Non-zero Components"] := Flatten[
	MapIndexed[
		If[SameQ[#1, 0], Nothing, Subscript[asc["Symbol"], Sequence @@ #2] -> #1]&,
		Normal[asc["Components"]],
		{ArrayDepth[asc["Components"], AllowedHeads -> List]}
	]
]

(*With indices*)

STensor[asc_?STensorAsQ /; SameQ[asc["Rank"], {0, 0}]][indices:(_?LetterQ | PatternSequence[_?LetterQ, _?LetterQ])]["Non-zero Components"] := If[asc["Components"] =!= 0, asc["Symbol"] -> asc["Components"], {}]

STensor[asc_?STensorAsQ /; UnsameQ[asc["Rank"], {0, 0}]
		][indices:(_?LetterQ | PatternSequence[_?LetterQ, _?LetterQ])]["Non-zero Components"] := Flatten[
	MapIndexed[
		If[SameQ[#1, 0], Nothing, Subscript[asc["Symbol"], Sequence @@ #2] -> #1]&,
		Normal[asc["Components"]],
		{ArrayDepth[asc["Components"], AllowedHeads -> List]}
	]
]


(* ::Section::Closed:: *)
(*Set Values*)


STensorAscKeys = {"Symbol", "Rank", "Symmetry", "Coordinate System", "Components", "Metric"};

Unprotect[Set];

STensor::NoSuchKey = "No such key \" `` \" in STensor.";

Set[(T_?STensorQ)[comp_String], value_] := Module[
	{asc = First[T]},
	If[FreeQ[STensorAscKeys, comp],
		Message[STensor::NoSuchKey, comp]; Abort[]
		];
	asc[comp] = value;
	T = STensor[asc];
	value
]
Protect[Set];


(* ::Section::Closed:: *)
(*Overload the Built-in Function*)


(* ::Subsection::Closed:: *)
(*System`FullSimplify*)


(*FullSimplify the components*)
System`FullSimplify[STensor[asc_?STensorAsQ], assum___, opt : OptionsPattern[]] := Module[
	{out = asc},
	out["Components"] = FullSimplify[asc["Components"], assum, opt];
	STensor[out]
]


(*FullSimplify the components*)
System`FullSimplify[STensor[asc_?STensorAsQ][ind : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]], assum___, opt : OptionsPattern[]] := Module[
	{out = asc},
	out["Components"] = FullSimplify[asc["Components"], assum, opt];
	STensor[out][ind]
]


(* ::Subsection::Closed:: *)
(*System`Simplify*)


(*Simplify the components*)
System`Simplify[STensor[asc_?STensorAsQ], assum___, opt : OptionsPattern[]] := Module[
	{out = asc},
	out["Components"] = Simplify[asc["Components"], assum, opt];
	STensor[out]
]


(*Simplify the components*)
System`Simplify[STensor[asc_?STensorAsQ][ind : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]], assum___, opt : OptionsPattern[]] := Module[
	{out = asc},
	out["Components"] = Simplify[asc["Components"], assum, opt];
	STensor[out][ind]
]


(* ::Subsection::Closed:: *)
(*System`Tensor**)


System`TensorSymmetry[STensor[asc_?STensorAsQ], slots___, opt : OptionsPattern[]] := 
	If[
		KeyExistsQ[asc, "Components"],
		TensorSymmetry[asc["Components"], slots, opt],
		If[
			KeyExistsQ[asc, "Symmetry"],
			asc["Symmetry"],
			{}
		]
	]


System`TensorRank[STensor[asc_?STensorAsQ], opt : OptionsPattern[]] := If[KeyExistsQ[asc, "Components"], TensorRank[asc["Components"], opt], Total[asc["Rank"]]]


System`TensorDimensions[STensor[asc_?STensorAsQ], opt : OptionsPattern[]] := 
	If[
		KeyExistsQ[asc, "Components"],
		TensorDimensions[asc["Components"], opt],
		If[
			KeyExistsQ[asc, "Coordinate System"],
			ConstantArray[Length[asc["Coordinate System"]], Total[asc["Rank"]]],
			{}
		]
]


(* ::Subsection::Closed:: *)
(*System`Inverse*)


(*get inverse of a metric*)
System`Inverse[g : STensor[asc_?STensorAsQ]] := Module[
{
	out = Association[]
},
	out["Symbol"] = asc["Symbol"];
	If[KeyExistsQ[asc, "Coordiante System"], out["Coordinate System"] = asc["Coordinate System"]];
	If[KeyExistsQ[asc, "Components"], out["Components"] = Inverse[asc["Components"]]];
	out["Rank"] = {2, 0};
	out["Metric"] = g;
	STensor[out]
]/; asc["Metric"] === True


(* ::Subsection::Closed:: *)
(*System`Tr*)


(*Calculate the trace of (1,1) rank tensor*)
System`Tr[T: STensor[asc_?STensorAsQ]] := Tr[asc["Components"]] /; asc["Rank"] === {1, 1}


System`Tr[T: STensor[asc_?STensorAsQ][
	indices : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]]
	] := Tr[asc["Components"]] /; asc["Rank"] === {1, 1}


System`Tr[T : STensor[asc_?STensorAsQ]] := TensorContract[
	asc["Components"] \[TensorProduct] (If[TrueQ[asc["Metric"]], asc, asc["Metric"]])["Components"],
	{{1, 3},{2, 4}}
] /; asc["Rank"] === {2, 0} && KeyExistsQ[asc, "Metric"]


System`Tr[T : STensor[asc_?STensorAsQ][
	indices : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]]
	] := TensorContract[
	asc["Components"] \[TensorProduct] (If[TrueQ[asc["Metric"]], asc, asc["Metric"]])["Components"],
	{{1,3},{2,4}}
] /; asc["Rank"] === {2, 0} && KeyExistsQ[asc, "Metric"]


System`Tr[T: STensor[asc_?STensorAsQ]] := TensorContract[
	asc["Components"] \[TensorProduct] Inverse[(If[TrueQ[asc["Metric"]], asc, asc["Metric"]])["Components"]],
	{{1,3},{2,4}}
] /; asc["Rank"] === {0, 2} && KeyExistsQ[asc, "Metric"]


System`Tr[T : STensor[asc_?STensorAsQ][
	indices : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]]
	] := TensorContract[
	asc["Components"] \[TensorProduct] Inverse[((If[TrueQ[asc["Metric"]], asc, asc["Metric"]])["Components"])["Components"]],
	{{1, 3}, {2, 4}}
] /; asc["Rank"] === {0, 2} && KeyExistsQ[asc, "Metric"]


(* ::Subsection::Closed:: *)
(*System`Symmetrize*)


(*default symmetric*)
System`Symmetrize[STensor[asc_?STensorAsQ]] := Module[
{
	out = asc
},
	out["Components"] = Normal[ Symmetrize[asc["Components"], Symmetric[Range[Plus@@asc["Rank"]]]]];
	
	out["Symmetry"] = Union[out["Symmetry"], {Symmetric[{{1, 2}}]}];
	
	STensor[out]
]


System`Symmetrize[STensor[asc_?STensorAsQ], sym_] := Module[
{
	out = asc
},
	out["Components"] = Normal[ Symmetrize[asc["Components"], sym]];
	
	out["Symmetry"] = Union[out["Symmetry"], If[Head[sym] === List, sym, {sym}]];
	
	STensor[out]
]


(*default symmetric*)
System`Symmetrize[STensor[asc_?STensorAsQ][ind: _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]]] := Module[
{
	out = asc
},
	out["Components"] = Normal[ Symmetrize[asc["Components"], Symmetric[Range[Plus @@ asc["Rank"]]]]];
	
	out["Symmetry"] = Union[out["Symmetry"], {Symmetric[{{1, 2}}]}];
	
	STensor[out][ind]
]


(*built-in input form*)
System`Symmetrize[STensor[asc_?STensorAsQ][ind: _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]], sym_] := Module[
{
	out = asc
},
	out["Components"] = Normal[ Symmetrize[asc["Components"], sym]];
	
	out["Symmetry"] = Union[out["Symmetry"], If[Head[sym] === List, sym, {sym}]];
	
	STensor[out][ind]
] /; FreeQ[sym, _String]


(*use index letters to represent symmetry*)
System`Symmetrize[STensor[asc_?STensorAsQ][ind: _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]], sym_] := Module[
{
	out = asc,
	symmetry = sym /. (First /@ PositionIndex[ Join@@(StringSplit[#, ""]& /@ {ind})])
},
	out["Components"] = Normal[ Symmetrize[asc["Components"], symmetry]];
	
	out["Symmetry"] = Union[out["Symmetry"], If[Head[symmetry] === List, symmetry, {symmetry}]];
	
	STensor[out][ind]
] /; MemberQ[sym, _String, All]


(* ::Section::Closed:: *)
(*Check Some Values*)


(* ::Subsection::Closed:: *)
(*Check*)


STensor::DifferentKeys = "`1` of tensor `2` and tensor `3` are different.";


STensorCheck["Metric"][
	T : STensor[ascT_?STensorAsQ],
	S : STensor[ascS_?STensorAsQ]
	] := Which[
		ascT == ascS, True,
		ascT["Metric"] === True, ascS["Metric"] === T,
		ascS["Metric"] === True, ascT["Metric"] === S,
		True, ascT["Metric"] === ascS["Metric"]
	]


STensorCheck["Metric"][
	T : STensor[ascT_?STensorAsQ][indicesT : Alternatives[_?LetterQ, PatternSequence[_?LetterQ, _?LetterQ]]],
	S : STensor[ascS_?STensorAsQ][indicesS : Alternatives[_?LetterQ, PatternSequence[_?LetterQ, _?LetterQ]]]
	] := Which[
		ascT == ascS, True,
		ascT["Metric"] === True, ascS["Metric"] === STensor[ascT],
		ascS["Metric"] === True, ascT["Metric"] === STensor[ascS],
		True, ascT["Metric"] === ascS["Metric"]
	]


STensorCheck[key_String][
	STensor[ascT_?STensorAsQ],
	STensor[ascS_?STensorAsQ]
	] := If[And @@ Join[KeyExistsQ[#, key]& /@ {ascT, ascS},{ascT[key] === ascS[key]}], True, False, False]


STensorCheck[key_String][
	STensor[ascT_?STensorAsQ][indicesT : Alternatives[_?LetterQ, PatternSequence[_?LetterQ, _?LetterQ]]],
	STensor[ascS_?STensorAsQ][indicesS : Alternatives[_?LetterQ, PatternSequence[_?LetterQ, _?LetterQ]]]
	] := If[And @@ Join[KeyExistsQ[#, key]& /@ {ascT, ascS},{ascT[key] === ascS[key]}], True, False, False]


(* ::Section::Closed:: *)
(*Computations*)


(* ::Text:: *)
(*Here is some note: I find that defining the scalar multiplication behind self contraction and tensor product will compute faster because the scalar will not do many times repeated meaningless computation. And about the order of self contraction and tensor product. No obvious difference found.*)


(* ::Subsection::Closed:: *)
(*(0,0)-rank tensor*)


STensor[asc_?STensorAsQ][___] := asc["Components"] /; asc["Rank"]=={0,0};

(*STensor[asc_?STensorAsQ] := asc["Components"] /; asc["Rank"]=={0,0};*)


(* ::Subsection::Closed:: *)
(*Plus*)


STensor /: Plus[
	STensor[ascT_?STensorAsQ][indicesT : _?LetterQ],
	S : STensor[ascS_?STensorAsQ][indicesS : _?LetterQ]] :=
	If[
		MatchQ[ascT["Rank"], {0, _?(#=!=0&)}],
		Plus[S, STensor[ascT]["", indicesT]],
		Plus[S, STensor[ascT][indicesT, ""]]
]


STensor /: Plus[
	STensor[ascT_?STensorAsQ][indicesT : _?LetterQ],
	S : STensor[ascS_?STensorAsQ][indicesS : PatternSequence[supindicesS_?LetterQ, subindicesS_?LetterQ]]] :=
	If[
		MatchQ[ascT["Rank"], {0, _?(#=!=0&)}],
		Plus[STensor[ascT]["", indicesT] , S],
		Plus[STensor[ascT][indicesT, ""], S]
]


STensor /: Plus[
	STensor[ascT_?STensorAsQ][indicesT : PatternSequence[supindicesT_?LetterQ, subindicesT_?LetterQ]],
	STensor[ascS_?STensorAsQ][indicesS : PatternSequence[supindicesS_?LetterQ, subindicesS_?LetterQ]]] := Module[
	{
		outasc,
		cyc1,
		cyc2
	},
	If[ascT["Rank"] =!= ascS["Rank"], Message[STensor::DifferentKeys, "Rank", ascT["Symbol"], ascS["Symbol"]];Abort[]];
	
	Map[
		If[KeyExistsQ[ascT, #] && KeyExistsQ[ascS, #] && !STensorCheck[#][STensor[ascT], STensor[ascS]],
			Message[STensor::DifferentKeys, #, ascT["Symbol"], ascS["Symbol"]]]&,
		{"Coordinate System", "Metric"}
	];
	
	outasc = ascT;
	{cyc1, cyc2} = FindPermutation @@@ (StringSplit[#, ""]& /@ {{supindicesS, supindicesT}, {subindicesS, subindicesT}});
	cyc2[[1]] += StringLength[supindicesT];
	outasc["Symbol"] = StringJoin[ascT["Symbol"], "+", ascS["Symbol"]];
	outasc["Symmetry"] = Intersection @@ (Lookup[#, "Symmetry", {}]& /@ {ascT, ascS});
	If[
		And @@ (KeyExistsQ["Components"]/@{ascT, ascS}),
		outasc["Components"] += TensorTranspose[ascS["Components"], PermutationProduct[cyc1, cyc2]];
	];
	If[KeyExistsQ[ascT, "Metric"] && KeyExistsQ[ascS, "Metric"], outasc["Metric"] = If[ascT["Metric"] === True, STensor[ascT], ascT["Metric"]]];
	STensor[outasc][indicesT]
];


(* ::Subsection::Closed:: *)
(*Self Contraction*)


STensor[asc_?STensorAsQ][sup_?LetterQ, sub_?LetterQ] /; IntersectingQ[StringSplit[sup, ""], StringSplit[sub, ""]] := Module[
{
	supInd = StringSplit[sup, ""],
	subInd = StringSplit[sub, ""],
	indices,
	outasc = asc,
	outsup, outsub
},
	outsup = Complement[supInd, subInd];
	outsub = Complement[subInd, supInd];
	
	If[
		KeyExistsQ[asc, "Components"],
		outasc["Components"] = TensorContract[asc["Components"], PositionIndex[Join[supInd, subInd]] /@ Intersection[supInd, subInd]];
	];
	outasc["Symmetry"] = {};
	outasc["Rank"] = Length /@ {outsup, outsub};
	
	STensor[outasc][StringJoin[outsup], StringJoin[outsub]]
]


(* ::Subsection::Closed:: *)
(*Tensor Product*)


(*T is a (n,0)-rank tensor and S is a (0,m)-rank tensor do not need to contract*)
STensor /: Times[
	STensor[ascT_?STensorAsQ][indicesT_?LetterQ],
	STensor[ascS_?STensorAsQ][indicesS_?LetterQ]] :=
	Module[
	{
		indT = StringSplit[indicesT, ""],
		indS = StringSplit[indicesS,""],
		IndicesPos,
		outasc = ascT,
		orderComplement,
		outInd
	},
	Map[
		If[KeyExistsQ[ascT, #] && KeyExistsQ[ascS, #] && !STensorCheck[#][STensor[ascT], STensor[ascS]],
			Message[STensor::DifferentKeys, #, ascT["Symbol"], ascS["Symbol"]]]&,
		{"Coordinate System", "Metric"}
	];
	outasc["Symbol"] = StringJoin[ascT["Symbol"], " ",ascS["Symbol"]];
	
	outasc["Rank"] = ascT["Rank"] + ascS["Rank"];
	
	If[
		And @@ (KeyExistsQ["Components"]/@{ascT, ascS}),
		outasc["Components"] = TensorProduct[ascT["Components"], ascS["Components"]]
	];
	
	outasc["Symmetry"] = Join[ ascT["Symmetry"], ascS["Symmetry"] /. {n_Integer :> n + Length[indT]}];
	
	If[And @@ (KeyExistsQ["Metric"] /@ {ascT, ascS}), outasc["Metric"] = If[ascT["Metric"] === True, STensor[ascT], ascT["Metric"]]];
	
	STensor[outasc][indicesT, indicesS]
] /; (!IntersectingQ @@ (StringSplit[#, ""]& /@ {indicesT, indicesS}) && (ascT["Rank"][[2]] == ascS["Rank"][[1]] == 0))



(*T is a (n,0)-rank tensor and S is a (0,m)-rank tensor need to contract*)

STensor /: Times[
	STensor[ascT_?STensorAsQ][indicesT_?LetterQ],
	STensor[ascS_?STensorAsQ][indicesS_?LetterQ]] :=
	Module[
	{
		indT = StringSplit[indicesT, ""],
		indS = StringSplit[indicesS,""],
		IndicesPos,
		outasc,
		orderComplement,
		outInd
	},
	Map[
		If[KeyExistsQ[ascT, #] && KeyExistsQ[ascS, #] && !STensorCheck[#][STensor[ascT], STensor[ascS]],
			Message[STensor::DifferentKeys, #, ascT["Symbol"], ascS["Symbol"]]]&,
		{"Coordinate System", "Metric"}
	];
	orderComplement = Function[{lis1, lis2}, DeleteCases[lis1, Alternatives @@ lis2]];
	
	outasc = ascT;
	
	IndicesPos = PositionIndex[Join[indT, indS]];
	
	outInd = orderComplement @@@ {{indT, indS}, {indS, indT}};
	
	If[
		And @@ (KeyExistsQ["Components"] /@ {ascT, ascS}),
		outasc["Components"] = TensorContract[TensorProduct[ascT["Components"], ascS["Components"]], IndicesPos[#]& /@ Intersection[indT, indS]]
	];
	
	outasc["Symbol"] = StringJoin[ascT["Symbol"], " ", ascS["Symbol"]];
	
	outasc["Rank"] = Length /@ outInd;
	(*need to find a algorithm to calc symmetry*)
	outasc["Symmetry"] = {};
	
	If[And @@ (KeyExistsQ["Metric"] /@ {ascT, ascS}), outasc["Metric"] = If[ascT["Metric"] === True, STensor[ascT], ascT["Metric"]]];
	
	(*judge if we got a (0,0)-rank tensor, which is a scalar need to return*)
	STensor[outasc][
			Sequence @@(
			If[Length[#]==1, First[#], #]&
				[(If[# === {}, Nothing, StringJoin @@ #]& /@ outInd)]
				)
			]
	] /; (IntersectingQ @@ (StringSplit[#, ""]& /@ {indicesT, indicesS}) && (ascT["Rank"][[2]] == ascS["Rank"][[1]] == 0))



(*Where T is (0,n)-rank tensor and S is (0,m)-rank tensor or (n,0) and (m,0)*)

STensor /: Times[
	STensor[ascT_?STensorAsQ][indicesT_?LetterQ],
	STensor[ascS_?STensorAsQ][indicesS_?LetterQ]] := 
	Module[
	{
		outasc
	},
	Map[
		If[KeyExistsQ[ascT, #] && KeyExistsQ[ascS, #] && !STensorCheck[#][STensor[ascT], STensor[ascS]],
			Message[STensor::DifferentKeys, #, ascT["Symbol"], ascS["Symbol"]]]&,
		{"Coordinate System", "Metric"}
	];
	outasc = ascT;
	
	If[
		And @@ (KeyExistsQ["Components"] /@ {ascT, ascS}),
		outasc["Components"] = TensorProduct[ascT["Components"], ascS["Components"]];
	];
	
	outasc["Symbol"] = StringJoin[ascT["Symbol"], " ", ascS["Symbol"]];
	
	outasc["Rank"] = ascT["Rank"] + ascS["Rank"];
	
	outasc["Symmetry"] = Join[ ascT["Symmetry"], ascS["Symmetry"] /. {n_Integer :> n + StringLength[indicesT]}];
	
	If[And @@ (KeyExistsQ["Metric"] /@ {ascT, ascS}), outasc["Metric"] = If[ascT["Metric"] === True, STensor[ascT], ascT["Metric"]]];
	
	STensor[outasc][StringJoin[indicesT, indicesS]]
] /; Or[ascT["Rank"][[2]] == ascS["Rank"][[2]] == 0, ascT["Rank"][[1]] == ascS["Rank"][[1]] == 0]




STensor /: Times[
	STensor[ascT_?STensorAsQ][indicesT_?LetterQ],
	STensor[ascS_?STensorAsQ][indicesS : PatternSequence[supindicesS_?LetterQ, subindicesS_?LetterQ]]] :=
	Which[
		MatchQ[ascT["Rank"], {x_Integer/;x!=0, 0}], Times[STensor[ascT][indicesT, ""], STensor[ascS][indicesS]],
		MatchQ[ascT["Rank"], {0, x_Integer/;x!=0}], Times[STensor[ascT]["", indicesT], STensor[ascS][indicesS]],
		True, Message[STensor::WrongIndicesnum, indicesT, ascT["Rank"]]
	]


(*more common situation: where T is rank{a,b} tensor and S is rank{c,d}*)
STensor /: Times[
	STensor[ascT_?STensorAsQ][indicesT : PatternSequence[supindicesT_?LetterQ, subindicesT_?LetterQ]],
	STensor[ascS_?STensorAsQ][indicesS : PatternSequence[supindicesS_?LetterQ, subindicesS_?LetterQ]]]:=
	Module[
{
		supT, subT, supS, subS,
		commonIndex, 
		sub,
		sup,
		orderComplement,
		outputIndex,
		IndicesPos,
		contractIndex,
		product,
		outputComponents,
		unArrangedIndex,
		TargetIndex,
		outasc = Association[]
},
	(*Check if two tensors are in the same coordinate and with same metric*)
	Map[
		If[KeyExistsQ[ascT, #] && KeyExistsQ[ascS, #] && !STensorCheck[#][STensor[ascT], STensor[ascS]],
			Message[STensor::DifferentKeys, #, ascT["Symbol"], ascS["Symbol"]]]&,
		{"Coordinate System", "Metric"}
	];
	
	(*The code can be short, but the following way shows my idea about computation*)
	orderComplement = DeleteCases[#1, Alternatives @@ #2]&;
	{supT, subT, supS, subS} = StringSplit[#, ""]&/@{supindicesT, subindicesT, supindicesS, subindicesS};
	commonIndex = Join[Intersection[supT, subT], Intersection[supS, subS], Intersection[supT, subS], Intersection[supS, subT]];
	sub = Join[subT, subS];
	sup = Join[supT, supS];
	
	(*The indices of the result tensor*)
	(*sort to make indices in order (not nessary)*)
	outputIndex = Sort/@{orderComplement[sup, sub], orderComplement[sub, sup]};
	
	(*place each indices corresponding to components*)
	IndicesPos = PositionIndex[Join[supT, subT, supS, subS]];
	
	(*compute the tensor product first*)
	product = TensorProduct[ascT["Components"], ascS["Components"]];
	
	(*find out the position of the indices need to constracte*)
	contractIndex = IndicesPos[#]& /@ commonIndex;
	
	(*contract the indices*)
	outputComponents = Simplify[TensorContract[product, contractIndex]];
	
	(*unArrangedIndex corresponds to outputComponents*)
	unArrangedIndex = orderComplement[Join[supT, subT, supS, subS], commonIndex];
	
	(*The indices of result tensor*)
	TargetIndex = Flatten[outputIndex];
	
	outasc["Symbol"] = StringJoin[ascT["Symbol"], " ", ascS["Symbol"]];
	
	outasc["Rank"] = Length /@ outputIndex;
	
	If[
		And @@ (KeyExistsQ["Components"] /@ {ascT, ascS}),
		outasc["Components"] = TensorTranspose[outputComponents, FindPermutation[unArrangedIndex, TargetIndex]];
	];
	(*need to find a algorithm to calc symmetry*)
	outasc["Symmetry"] = {};
	
	If[KeyExistsQ[ascT, #], outasc[#] = ascT[#]]& /@ {"Coordinate System"};
	
	If[And @@ (KeyExistsQ["Metric"] /@ {ascT, ascS}), outasc["Metric"] = If[ascT["Metric"] === True, STensor[ascT], ascT["Metric"]]];
	
	STensor[outasc][Sequence @@ (StringJoin /@ outputIndex)]
];



(* ::Subsection::Closed:: *)
(*Wedge*)


Wedge::NotDifferentialForm = "`1` is not a differential form."


STensor /: Wedge[
	STensor[ascT_?STensorAsQ][indicesT_?LetterQ],
	STensor[ascS_?STensorAsQ][indicesS_?LetterQ]] :=
	Module[
	{
		subT = StringSplit[indicesT, ""],
		subS = StringSplit[indicesS, ""],
		asc = ascT
	},
	Which[
		!MatchQ[ascT["Rank"], {0, _}], Message[Wedge::NotDifferentialForm, ascT["Symbol"]],
		!MatchQ[ascS["Rank"], {0, _}], Message[Wedge::NotDifferentialForm, ascS["Symbol"]]
	];
	asc["Symbol"] = StringJoin[ascT["Symbol"], "\[Wedge]", ascS["Symbol"]];
	asc["Rank"] = Plus @@ (#["Rank"]& /@ {ascT, ascS});
	If[
		And @@ (KeyExistsQ["Components"] /@ {ascT, ascS}),
		asc["Components"] = TensorWedge[ascT["Components"], ascS["Components"]];
	];
	asc["Symmetry"] = Antisymmetric[Range[Total[Length /@ {subT, subS}]]];
	STensor[asc][StringJoin[indicesT, indicesS]]
]
STensor /: Wedge[
	T : STensor[_?STensorAsQ][_?LetterQ],
	S : Repeated[STensor[_?STensorAsQ][_?LetterQ]]]:= Wedge[T, Wedge[S]]


(* ::Subsection::Closed:: *)
(*Derivative Operator*)


Grad[Times[f_?FreeQ[_STensor], T: STensor[asc_?STensorAsQ][indices: _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]] /; KeyExistsQ[asc, "Metric"]], dIndex_] :=
	Times[ D[f, dIndex], Grad[T[indices], dIndex]]
	
STensor /: Grad[T: STensor[asc_?STensorAsQ][indices_?LetterQ]/;KeyExistsQ[asc, "Metric"], dIndex_] := Which[
	MatchQ[asc["Rank"], {_, 0}], Grad[STensor[asc][indices, ""], dIndex],
	MatchQ[asc["Rank"], {0, _}], Grad[STensor[asc]["", indices], dIndex]
]
STensor /: Grad[T: STensor[asc_?STensorAsQ][indices: PatternSequence[_?LetterQ, _?LetterQ]]/;KeyExistsQ[asc, "Metric"], dIndex_] := 
Module[
{
	coordinates = asc["Coordinate System"],
	components = asc["Components"],
	\[CapitalGamma] = ChristoffelSymbol[If[asc["Metric"] === True, asc["Components"], asc["Metric"]["Components"]], asc["Coordinate System"]],
	supIndices, subIndices,
	suplen, sublen,
	outasc = Association[]
},
	supIndices = StringSplit[{indices}[[1]], ""];
	subIndices = StringSplit[{indices}[[2]], ""];
	suplen = Length[supIndices];
	sublen = Length[subIndices];
	
	outasc["Rank"] = asc["Rank"] + {0, 1};
	
	outasc["Symbol"] = StringJoin["\[Del](", asc["Symbol"], ")"];
	
	outasc["Symmetry"] = asc["Symmetry"];
	
	outasc["Metric"] = If[asc["Metric"] === True, STensor[asc], asc["Metric"]];
	
	If[
		KeyExistsQ[asc, "Coordinate System"],
		outasc["Coordinate System"] = coordinates
	];
	
	If[
		KeyExistsQ[asc, "Components"],
		outasc["Components"] = D[components, {coordinates}];
		
		(*If the Christoffel Symbol is zero tensor, it wouldn't need to calculate the rest part*)
		If[
			AnyTrue[Flatten[\[CapitalGamma]], # =!= 0&],
			(*calculate*)
			(*use a subscript of \[CapitalGamma] to contract one of supscripts of T*)
			outasc["Components"] +=(
			Plus @@
				(
					(
						Transpose[(TensorContract[Transpose[\[CapitalGamma] \[TensorProduct] components, 1 <-> #],{{1, 2}}]&[#]),
						RotateRight[ Range[1 + suplen + sublen], 1] ]
						(*The inner Transpose transposes the supscript of \[CapitalGamma] with the contracted supscript index of T*)
						(*The outer Transpose make the rest one sub index components of \[CapitalGamma] to the last positon*)
					)& /@ Range[4, 3 + suplen]
				)
			-
			Plus @@ 
				(
					(
						Transpose[(TensorContract[Transpose[\[CapitalGamma] \[TensorProduct] components, 2 <-> #],{{1, 2}}]&[#]),
						RotateRight[ Range[1 + suplen + sublen], 1] ]
						(*The inner Transpose transposes the supscript of \[CapitalGamma] with the contracted supscript index of T*)
						(*The outer Transpose make the rest one sub index components of \[CapitalGamma] to the last positon*)
					)& /@ Range[4 + suplen, 3 + suplen + sublen]
				)
			);
		];
		outasc["Components"] = Simplify[outasc["Components"]];
	];
	
	STensor[outasc][StringJoin[supIndices], StringJoin[subIndices, ToString[dIndex]]]
]


(*OrdinaryDerivative*)
D::OrdinaryDerivative = "Coordinate System is needed for oridnary derivative.";

STensor /: D[T : STensor[asc_?STensorAsQ][indices_?LetterQ]/;KeyExistsQ[asc, "Coordinate System"], dIndex_] := Which[
	MatchQ[asc["Rank"], {0, _}], D[STensor[asc]["", indices], dIndex],
	MatchQ[asc["Rank"], {_, 0}], D[STensor[asc][indices, ""], dIndex]
]

STensor /: D[T : STensor[asc_?STensorAsQ][indices : PatternSequence[supindices_?LetterQ, subindices_?LetterQ]], dIndex_] := Module[
{
	coordinates = asc["Coordinate System"],
	dimension = Length[asc["Coordinate System"]],
	ind = ToString[dIndex],
	outasc = Association[]
},
	outasc["Rank"] = asc["Rank"] + {0, 1};
	
	outasc["Symbol"] = StringJoin["\[PartialD](", asc["Symbol"], ")"];
	
	If[
		KeyExistsQ[asc, "Coordinate System"],
		outasc["Coordinate System"] = coordinates,
		Message[D::OrdinaryDerivative];
	];
	
	If[KeyExistsQ[asc, "Metric"], outasc["Metric"] = If[asc["Metric"] === True, STensor[asc], asc["Metric"]]];
	
	If[
		KeyExistsQ[asc, "Components"],
		outasc["Components"] = D[asc["Components"], {coordinates}]
	];
	
	STensor[outasc][supindices, StringJoin[subindices, ind]]
]


(* ::Subsubsection:: *)
(**)


(* ::Subsection::Closed:: *)
(*Scalar Multiplication*)


STensor /: Times[k_ /; FreeQ[k, STensor], STensor[asc_?STensorAsQ]] :=
Module[{outasc = asc},
	outasc["Symbol"] = StringJoin["(", ToString[InputForm[k]], ") ", asc["Symbol"]];
	
	If[KeyExistsQ[asc, "Components"],outasc["Components"] *= k];
	
	outasc["Symmetry"] = If[Simplify[k] === 0, {ZeroSymmetric[{}]}, asc["Symmetry"]];
	
	If[asc["Metric"] === True, outasc["Metric"] = STensor[asc]];
	
	STensor[outasc]
];


STensor /: Times[k_ /; FreeQ[k, STensor], STensor[asc_?STensorAsQ][indices : _?LetterQ | PatternSequence[_?LetterQ, _?LetterQ]]] :=
Module[{outasc = asc},
	outasc["Symbol"] = StringJoin["(", ToString[InputForm[k]], ") ", asc["Symbol"]];
	
	If[KeyExistsQ[asc, "Components"],outasc["Components"] *= k];
	
	outasc["Symmetry"] = If[Simplify[k] === 0, {ZeroSymmetric[{}]}, asc["Symmetry"]];
	
	If[asc["Metric"] === True, outasc["Metric"] = STensor[asc]];
	
	STensor[outasc][indices]
];


(* ::Section::Closed:: *)
(*Some Useful Functions*)


CalcTensor::DimensionError = "The dimension of metric components - `1` - does not match with the dimension of the coordinate system - `2`."


(* ::Subsection::Closed:: *)
(*Compute with Metric Components Array and coordinates*)


(* ::Subsubsection::Closed:: *)
(*Christoffel Symbol*)


(*Christoffel Symbol*)
ChristoffelSymbol[g_?ArrayQ, coordinateSystem_List] := Module[
	{
		invg = Inverse[g],(*inverse of metric components*)
		dimension = Length @ coordinateSystem,(*dimension of manifold*)
		\[Gamma],(*Christoffel Symbol Components Calculating Function*)
		\[CapitalGamma](*Christoffel Symbol Components Matrix*)
	},
	If[
		First @ Dimensions @ g != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError, First @ Dimensions @ g, coordinateSystem];
		Abort[]
	];
	
	\[Gamma][\[Sigma]_, \[Mu]_, \[Nu]_] := 1/2 Sum[ invg[[\[Sigma], \[Rho]]] (D[g[[\[Rho], \[Mu]]], coordinateSystem[[\[Nu]]] ]+D[ g[[\[Nu], \[Rho]]], coordinateSystem[[\[Mu]]] ]-D[ g[[\[Mu], \[Nu]]], coordinateSystem[[\[Rho]]] ]),{\[Rho], dimension}];
	
	(*Use the symmetry of the sub indices to reduce half of computation*)
	\[CapitalGamma] = Simplify @ Array[If[ #2<=#3, \[Gamma][#1, #2, #3], Null]&, ConstantArray[dimension, 3]]; (*components matrix*)
	
	Array[If[#2>#3, \[CapitalGamma][[#1, #2, #3]]=\[CapitalGamma][[#1, #3, #2]]]&, ConstantArray[dimension, 3]];
	
	\[CapitalGamma]
];


(* ::Subsubsection::Closed:: *)
(*Riemann Tensor*)


(*Riemann Tensor*)
(*Calculate with metric given*)
RiemannTensor[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := Module[
	{
		invg = Inverse[g],(*inverse of metric g*)
		dimension = Length @ coordinateSystem,(*dimension of space*)
		\[CapitalGamma],(*Christoffel Symbol Component Matrix*)
		r,(*Riemann Tensor Conponent Calculating Function*)
		Riemann(*Riemann Tensor Component Matrix*)
	},
	If[
		First @ Dimensions @ g != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError, First @ Dimensions @ g, coordinateSystem];
		Abort[]
	];
	(*Compute the components of Riemann tensor by "Coordinates method" (maybe it's the name of method) *)
	
	(*Compute Christoffel Symbol first*)
	\[CapitalGamma] = ChristoffelSymbol[g, coordinateSystem];
	
	r[\[Rho]_, \[Mu]_, \[Nu]_, \[Sigma]_] := D[
		\[CapitalGamma][[\[Rho], \[Mu], \[Sigma]]], coordinateSystem[[\[Nu]]]] - D[ \[CapitalGamma][[\[Rho], \[Nu], \[Sigma]]], coordinateSystem[[\[Mu]]]] + 
		Sum[\[CapitalGamma][[\[Lambda], \[Sigma], \[Mu]]] \[CapitalGamma][[\[Rho], \[Nu], \[Lambda]]] - \[CapitalGamma][[\[Lambda], \[Sigma], \[Nu]]] \[CapitalGamma][[\[Rho], \[Mu], \[Lambda]]], {\[Lambda],dimension}];
	(*Reduce half of computation by the antisymmetry of Riemann Tensor*)
	(*There are more symmetries and antisymmetries of Riemann Tensor I don't use here, which would spend more time*)
	(*In fact, the independent components of a n-dimension Riemann tensor is (n^2-1)n^2/12*)
	(*When n is equal to 3, the number is 6, which would lead to the Weyl Tensor vanishing*)
	Riemann = Simplify@Array[If[#2<=#3,r[#1, #2, #3, #4],Null]&, ConstantArray[dimension, 4]];
	
	Array[If[#2>#3, Riemann[[#1, #2, #3, #4]] = -Riemann[[#1, #3, #2, #4]]]&, ConstantArray[dimension, 4]];
	
	(*Print[Subsuperscript["R","\[Mu]\[Nu]\[Sigma]","   \[Rho]"]->MatrixForm@Riemann];*)
	
	Riemann
];


(*Calculate with Christoffel Symbol given*)
RiemannTensor[\[CapitalGamma]_?ArrayQ/;ArrayDepth[\[CapitalGamma]]==3, coordinateSystem_List] := Module[
	{
		dimension = Length @ coordinateSystem,(*dimension of space*)
		r,(*Riemann Tensor Conponent Calculating Function*)
		Riemann(*Riemann Tensor Component Matrix*)
	},
	If[
		First @ Dimensions @ \[CapitalGamma] != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError];
		Abort[]
	];
	(*Compute the components of Riemann tensor by "Coordinates method" (maybe it's the name of method) *)
	
	r[\[Rho]_, \[Mu]_, \[Nu]_, \[Sigma]_] := D[
		\[CapitalGamma][[\[Rho], \[Mu], \[Sigma]]], coordinateSystem[[\[Nu]]]] - D[ \[CapitalGamma][[\[Rho], \[Nu], \[Sigma]]], coordinateSystem[[\[Mu]]]] + 
		Sum[\[CapitalGamma][[\[Lambda], \[Sigma], \[Mu]]] \[CapitalGamma][[\[Rho], \[Nu], \[Lambda]]] - \[CapitalGamma][[\[Lambda], \[Sigma], \[Nu]]] \[CapitalGamma][[\[Rho], \[Mu], \[Lambda]]], {\[Lambda],dimension}];
	(*Reduce half of computation by the antisymmetry of Riemann Tensor*)
	(*There are more symmetries and antisymmetries of Riemann Tensor I don't use here, which would spend more time*)
	(*In fact, the independent components of a n-dimension Riemann tensor is (n^2-1)n^2/12*)
	(*When n is equal to 3, the number is 6, which would lead to the Weyl Tensor vanishing*)
	Riemann = Simplify@Array[If[#2<=#3,r[#1, #2, #3, #4],Null]&, ConstantArray[dimension, 4]];
	
	Array[If[#2>#3, Riemann[[#1, #2, #3, #4]] = -Riemann[[#1, #3, #2, #4]]]&, ConstantArray[dimension, 4]];
	
	(*Print[Subsuperscript["R","\[Mu]\[Nu]\[Sigma]","   \[Rho]"]->MatrixForm@Riemann];*)
	
	Riemann
];


(* ::Subsubsection::Closed:: *)
(*Ricci Tensor*)


(*Ricci Tensor*)
(*Calculate with metric given*)
RicciTensor[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := Module[
{
	det = Det[g],
	invg = Inverse[g],(*inverse of metric components*)
	dimension = Length @ coordinateSystem,(*dimension of space*)
	\[Gamma],(*Contracted Christoffel Symbol*)
	\[CapitalGamma],(*Christoffel Symbol*)
	R,(*Riemann Tensor Component Matrix*)
	ricci,(*Ricci Tensor Component Calculating Function*)
	Ricci(*Ricci Tensor Component Matrix*)
},
	If[
		First @ Dimensions @ g != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError, First @ Dimensions @ g, coordinateSystem];
		Abort[]
	];
	(*Calculation part*)
	
(*
	(*Calculate with Riemann Tensor*)
	R = RiemannTensor[g,coordinateSystem];
	ricci[\[Mu]_,\[Nu]_] := Sum[ R[[\[Mu],\[Sigma],\[Nu],\[Sigma]]], {\[Sigma],dimension}];*)

	
	(*Calculate with Christoffel Symbol using a given formular*)
	\[CapitalGamma] = Simplify @ ChristoffelSymbol[g, coordinateSystem];
	(*Calculate the contracted Christoffel Symbol with a theorem*)
	\[Gamma] = Simplify[ 1/(2 det) * D[det, {coordinateSystem}] ];
	
	ricci[\[Mu]_, \[Sigma]_] := 
		Sum[ D[\[CapitalGamma][[\[Nu], \[Mu], \[Sigma]]], coordinateSystem[[\[Nu]]]] - Sum[ \[CapitalGamma][[\[Lambda], \[Nu], \[Sigma]]] * \[CapitalGamma][[\[Nu], \[Lambda], \[Mu]]], {\[Lambda], dimension}], {\[Nu], dimension}]
		- D[\[Gamma][[\[Sigma]]], coordinateSystem[[\[Mu]]]] + Sum[\[CapitalGamma][[\[Lambda], \[Mu], \[Sigma]]] * \[Gamma][[\[Lambda]]], {\[Lambda], dimension}];
		
	(*Reduce the computation complexity by tensor symmetry*)
	
	Ricci = Simplify @ Array[If[#1<=#2, ricci[#1,#2], Null]&, {dimension, dimension}];
	
	Array[If[#1>#2, Ricci[[#1,#2]] = Ricci[[#2,#1]]]&, {dimension, dimension}];
	
	(*Print[Subscript["R","\[Mu]\[Nu]"]->MatrixForm@Ricci];*)
	Ricci
];


(*Calculate with Christoffel Symbol given*)
RicciTensor[\[CapitalGamma]_?ArrayQ/;ArrayDepth[\[CapitalGamma]]==3, coordinateSystem_List] := Module[
{
	dimension = Length @ coordinateSystem,(*dimension of space*)
	\[Gamma],(*Contracted Christoffel Symbol*)
	R,(*Riemann Tensor Component Matrix*)
	ricci,(*Ricci Tensor Component Calculating Function*)
	Ricci(*Ricci Tensor Component Matrix*)
},
	If[
		First @ Dimensions @ \[CapitalGamma] != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError];
		Abort[]
	];
	(*Calculation part*)

	(*Calculate the contracted Christoffel Symbol with a theorem*)
	\[Gamma] = Simplify[Array[Sum[\[CapitalGamma][[\[Sigma],#,\[Sigma]]], {\[Sigma], dimension}]&, dimension]];
	
	ricci[\[Mu]_, \[Sigma]_] := 
		Sum[ D[\[CapitalGamma][[\[Nu], \[Mu], \[Sigma]]], coordinateSystem[[\[Nu]]]] - Sum[ \[CapitalGamma][[\[Lambda], \[Nu], \[Sigma]]] * \[CapitalGamma][[\[Nu], \[Lambda], \[Mu]]], {\[Lambda], dimension}], {\[Nu], dimension}]
		- D[\[Gamma][[\[Sigma]]], coordinateSystem[[\[Mu]]]] + Sum[\[CapitalGamma][[\[Lambda], \[Mu], \[Sigma]]] * \[Gamma][[\[Lambda]]], {\[Lambda], dimension}];
		
	(*Reduce the computation complexity by tensor symmetry*)
	
	Ricci = Simplify @ Array[If[#1<=#2, ricci[#1,#2], Null]&, {dimension, dimension}];
	
	Array[If[#1>#2, Ricci[[#1,#2]] = Ricci[[#2,#1]]]&, {dimension, dimension}];
	
	(*Print[Subscript["R","\[Mu]\[Nu]"]->MatrixForm@Ricci];*)
	Ricci
];


(* ::Subsubsection::Closed:: *)
(*Ricci Scalar*)


(*Ricci Scalar*)
(*Calculate with metric given*)
RicciScalar[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := Module[
{
	dimension = Length @ coordinateSystem,
	invg = Inverse[g],
	Ricci
},
	If[
		First @ Dimensions @ g != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError, First @ Dimensions @ g, coordinateSystem];
		Abort[]
	];
	
	Ricci = Simplify @ RicciTensor[g, coordinateSystem];
	Sum[Ricci[[\[Mu],\[Nu]]] invg[[\[Mu],\[Nu]]],{\[Mu], dimension},{\[Nu], dimension}]
];


(* ::Subsubsection::Closed:: *)
(*Einstein Tensor*)


(*Einstein Tensor*)
(*Calculate with metric given*)
EinsteinTensor[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := Module[
{
	invg = Inverse[g],
	dimension = Length @ coordinateSystem,
	RicciT,
	RicciS
},
	If[
		First @ Dimensions @ g != Length @ coordinateSystem,
		Message[CalcTensor::DimensionError, First @ Dimensions @ g, coordinateSystem];
		Abort[]
	];
	
	(*Compute the Ricci Tensor first*)
	RicciT = Simplify @ RicciTensor[g, coordinateSystem];
	
	(*Compute the Ricci Scalar*)
	RicciS = Sum[RicciT[[\[Mu],\[Nu]]] invg[[\[Mu],\[Nu]]],{\[Mu], dimension},{\[Nu], dimension}];
	(*Return the result*)
	RicciT - RicciS / 2 * g
]


(* ::Subsubsection::Closed:: *)
(*Weyl Tensor*)


WeylTensor::WeylTensorUndefined = "Weyl Tensor is only defined on the manifold where dimension is greater than 2."
(*Calculate with given metric*)
WeylTensor[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := Module[
{
	dimension = Length @ coordinateSystem,
	invg = Inverse[g],
	Riemann = RiemannTensor[g, coordinateSystem],
	R,
	ricci,
	Ricci,
	ricciscalar,
	gR,
	gg
},
	If[
		dimension <= 2,
		Message[WeylTensor::WeylTensorUndefined];
		Abort[]
	];
	
	(*Compute Ricci Tensor first*)
	ricci[\[Mu]_, \[Nu]_] := Sum[ Riemann[[\[Sigma], \[Mu], \[Sigma], \[Nu]]], {\[Sigma], dimension}];
	
	(*Ricci Tensor*)
	Ricci = Simplify @ Array[If[#1 <= #2, ricci[#1, #2], Null]&, {dimension, dimension}];
	
	Array[If[#1>#2, Ricci[[#1, #2]] = Ricci[[#2, #1]]]&, {dimension, dimension}];
	
	(*Ricci Scalar*)
	ricciscalar = Simplify @ Sum[Ricci[[\[Mu], \[Nu]]] invg[[\[Mu], \[Nu]]], {\[Mu], dimension}, {\[Nu], dimension}];
	
	(*Store some useful intermediate results to reduce computation complexity*)
	gR = TensorProduct[g, Ricci];
	gg = TensorProduct[g, g];
	
	(*Use the definition to calculate each components and make up to an array*)
	Array[
		Sum[Riemann[[i, #1, #2, #3]] g[[i, #4]], {i, dimension}]
		- (gR[[#1, #3, #4, #2]] - gR[[#1, #4,#3, #2]] - gR[[#2, #3, #4, #1]] + gR[[#2, #4, #3, #1]]) / (dimension - 2)
		+ (ricciscalar / ((dimension - 1) * (dimension - 2))) * (gg[[#1, #3, #4,#2]] - gg[[#1, #4, #3,#2]])&,
		ConstantArray[dimension, 4]
	]
]


(* ::Subsubsection::Closed:: *)
(*Volume Element*)


VolumeElement[g_?ArrayQ/;ArrayDepth[g]==2, coordinateSystem_List] := 
	With[{u = Join[ConstantArray[0, Length[coordinateSystem] - 1], {1}]},
			Abs[Det[g]] * Normal[TensorWedge @@ Table[RotateRight[u, i], {i, Length[coordinateSystem]}]]
		]


(* ::Subsection::Closed:: *)
(*Compute with STensor Object*)


(*The former functions are useful. So we use them directly*)


(* ::Subsubsection::Closed:: *)
(*Christoffel Symbol*)


(*Here I guarantee the Rank is {0,2}, but the components matrix should be symmetric, non-degenerate and positive definite*) 


(*Compute with metirc*)
ChristoffelSymbol[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {0,2} && asc["Metric"] === True] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {1, 2};
	outasc["Symbol"] = StringJoin["\[CapitalGamma](", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = ChristoffelSymbol[asc["Components"], asc["Coordinate System"]];
	outasc["Symmetry"] = {Symmetric[{2, 3}]};
	outasc["Metric"] = metric;
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Riemann Tensor*)


(*Compute with metirc*)
RiemannTensor[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {1, 2} || (asc["Rank"] === {0,2} && asc["Metric"] === True)] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {1, 3};
	outasc["Symbol"] = StringJoin["Riemann(", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = RiemannTensor[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = If[asc["Rank"] === {1, 2}, asc["Metric"], metric];
	outasc["Symmetry"] = {Antisymmetric[{2, 3}]};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Ricci Tensor*)


(*Compute with metirc*)
RicciTensor[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {1, 2} || (asc["Rank"] === {0,2} && asc["Metric"] === True)] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {0, 2};
	outasc["Symbol"] = StringJoin["RicciT(", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = RicciTensor[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = If[asc["Rank"] === {1, 2}, asc["Metric"], metric];
	outasc["Symmetry"] = {Symmetric[{1, 2}]};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Ricci Scalar*)


(*Compute with metric*)
(*Compute with metirc*)
RicciScalar[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {0,2} && asc["Metric"] === True] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {0, 0};
	outasc["Symbol"] = StringJoin["RicciS(", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = RicciScalar[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = metric;
	outasc["Symmetry"] = {};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Einstein Tensor*)


(*Compute with metirc*)
EinsteinTensor[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {0,2} && asc["Metric"] === True] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {0, 2};
	outasc["Symbol"] = StringJoin["G(", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = EinsteinTensor[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = metric;
	outasc["Symmetry"] = {Symmetric[{1, 2}]};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Weyl Tensor*)


(*Compute with metirc*)
WeylTensor[metric : STensor[asc_?STensorAsQ]/;asc["Rank"] === {0,2} && asc["Metric"] === True] := 
Module[
{
	outasc = Association[]
},
	outasc["Rank"] = {0, 4};
	outasc["Symbol"] = StringJoin["Weyl(", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = WeylTensor[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = metric;
	outasc["Symmetry"] = {{Cycles[{{1, 2}}], -1}, {Cycles[{{3, 4}}], -1}};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Volume Element*)


VolumeElement[metric : STensor[asc_?STensorAsQ]/; asc["Rank"] === {0,2} && asc["Metric"] === True] := 
Module[
{
	outasc = Association[]
	},
	outasc["Rank"] = {0, Length[asc["Coordinate System"]]};
	outasc["Symbol"] = StringJoin["\[Epsilon](", asc["Symbol"], ")"];
	outasc["Coordinate System"] = asc["Coordinate System"];
	outasc["Components"] = VolumeElement[asc["Components"], asc["Coordinate System"]];
	outasc["Metric"] = metric;
	outasc["Symmetry"] = {Antisymmetric[ Range[ Length[asc["Coordinate System"]] ] ]};
	STensor[outasc]
]


(* ::Subsubsection::Closed:: *)
(*Line Element*)


LineElement[metric : STensor[asc_?STensorAsQ]/; asc["Rank"] === {0,2} && asc["Metric"] === True] := Dot[DifferentialD /@ asc["Coordinate System"], metric["Components"], DifferentialD /@ asc["Coordinate System"]];


(* ::Section::Closed:: *)
(*Coordinate Transformation*)


SCoordinateTransform[T : STensor[asc_?STensorAsQ], targetCods_List, Trans:_List|_Association, invTrans:_List|_Association] :=
Module[
{
	out = asc
},
	out["Coordinate System"] = targetCods;
	out["Components"] = componentsTransform[asc["Components"], asc["Coordinate System"], targetCods, asc["Rank"], Trans, invTrans];
	STensor[out]
] /; AllTrue[Join[Trans, invTrans], Head[#]===Rule&]


(*use list or assciation of rules to represent the transformation*)
componentsTransform[comp_?ArrayQ, originalCods_List, targetCods_List, rank_List, Trans:_List|_Association, invTrans:_List|_Association] :=
Module[
		{
			x, (*local coordinates variable*)
			jacobian, (*jacobian matrix*)
			jacobianInv, (*inverse javobian matrix*)
			dimension = First[TensorDimensions[comp]], (*dimension of manifold*)
			term,
			cof,
			orTotar = MapThread[Rule, {originalCods, Values[Trans]}]
		},
		(*a formal symbol to represent coordinates*)
		(*use the symbols of target coordinate system to represent the jacobian and jacobianInv*)
		jacobian = D[Values[Trans], {originalCods}]/. orTotar;
		jacobianInv = Simplify[D[Values[invTrans], {targetCods}]];
		
(*		Echo[jacobian];
		Echo[jacobianInv];*)
		
		(*coeffcient apart from components, step by step to construct the tensor product*)
		(*It can be split into product of two terms - sup and sub*)
		(*sumsup and sumsub are indices that would be used in Einstein summation*)
		cof[sup_, sub_, sumsup_, sumsub_] := Times[
			Array[jacobianInv[[sumsup[[#]], sub[[#]]]]&, {Length[sub]}, 1, Times],
			Array[jacobian[[sup[[#]], sumsub[[#]]]]&, {Length[sup]}, 1, Times]
			];
		
		(*calculate each term, after Einstein summation convention*)
		term[sup_, sub_] :=
			Array[
				With[
				{
					sumsup = {##}[[rank[[1]] + 1 ;; ]],
					sumsub = {##}[[ ;; rank[[1]]]]
				},
					cof[sup, sub, sumsup, sumsub] comp[[##]] /. orTotar
				]&
				,
				Dimensions[comp], 1, Plus
			];
		
		(*build the components array*)
		Array[
			term[
				{##}[[rank[[2]] + 1 ;; ]],
				{##}[[ ;; rank[[2]]]]]&
				,
			Dimensions[comp]
		]
	]


(*use built-in chart in CoordinateTransformData*)
SCoordinateTransform::LackofData = "No enough data of transormation between `1` and `2`, please input mannually."
SCoordinateTransform[T : STensor[asc_?STensorAsQ], targetsCods_List,
	Rule[originalChart_String, targetChar_String] | TwoWayRule[originalChart_String, targetChar_String]] := Module[
{
	Trans,
	invTrans,
	dimension = Length[asc["Coordinate System"]]
},
	Trans = CoordinateTransformData[{originalChart -> targetChar, dimension}, "Mapping"];
	invTrans = CoordinateTransformData[{targetChar -> originalChart, dimension}, "Mapping"];
	If[
		Head[Trans] === Head[invTrans] === Function,
		SCoordinateTransform[T, targetsCods, Trans, invTrans],
		Message[SCoordinateTransform::LackofData, originalChart, targetChar];Abort[]
	]
]


(*use pure functions to represent the transformation as CoordianteTransformData gives*)
SCoordinateTransform[STensor[asc_?STensorAsQ], targetCods_List, Trans_Function, invTrans_Function] := Module[
{
	out = asc
},
	out["Coordinate System"] = targetCods;
	out["Components"] = componentsTransform[asc["Components"], asc["Coordinate System"], targetCods, asc["Rank"], Trans, invTrans];
	STensor[out]
]


componentsTransform[comp_?ArrayQ, originalCods_List, targetCods_List, rank_List, Trans_Function, invTrans_Function] :=
	Module[
		{
			x, (*local coordinates variable*)
			syms, (*local coordinates symbol list*)
			jacobian, (*jacobian matrix*)
			jacobianInv, (*inverse javobian matrix*)
			dimension = First[TensorDimensions[comp]], (*dimension of manifold*)
			term,
			cof,
			orTotar = MapThread[Rule, {originalCods, invTrans[targetCods]}]
		},
		(*a formal symbol to represent coordinates*)
		syms = Array[x, dimension];
		(*use the symbols of target coordinate system to represent the jacobian and jacobianInv*)
		jacobian = Simplify[D[Trans[syms], {syms}] /. {x[i_] :> originalCods[[i]]} /. orTotar];
		jacobianInv = D[invTrans[syms], {syms}] /. {x[i_] :> targetCods[[i]]};
		
(*		Echo[jacobian];
		Echo[jacobianInv];*)
		
		(*coeffcient apart from components, step by step to construct the tensor product*)
		(*It can be split into product of two terms - sup and sub*)
		(*sumsup and sumsub are indices that would be used in Einstein summation*)
		cof[sup_, sub_, sumsup_, sumsub_] := Times[
			Array[jacobianInv[[sumsup[[#]], sub[[#]]]]&, {Length[sub]}, 1, Times],
			Array[jacobian[[sup[[#]], sumsub[[#]]]]&, {Length[sup]}, 1, Times]
			];
		
		(*calculate each term, after Einstein summation convention*)
		term[sup_, sub_] :=
			Array[
				With[
				{
					sumsup = {##}[[rank[[1]] + 1 ;; ]],
					sumsub = {##}[[ ;; rank[[1]]]]
				},
					cof[sup, sub, sumsup, sumsub] comp[[##]] /. orTotar
				]&
				,
				Dimensions[comp], 1, Plus
			];
		
		(*build the components array*)
		Array[
			term[
				{##}[[rank[[2]] + 1 ;; ]],
				{##}[[ ;; rank[[2]]]]]&
				,
			Dimensions[comp]
		]
	]


(* ::Section::Closed:: *)
(*End Context*)


Protect @@ Private`syms
Protect @@ Private`systemsyms


End[]


EndPackage[]
