(* ::Package:: *)

(* ::Section:: *)
(*parseJTask*)


parseJTask::usage="parseJTask[file,conic,defaultVarName,defaultBarVarName] translates a MOSEK JTASK file into a Mathematica optimization call. The parameter `conic` (default: False) specifies whether the constraints should be expressed in conic form using VectorGreaterEqual when possible. The default variable and barvariable names are x and X.";


parseJTaskSolution::usage=
"parseJTaskSolution[file,defaultVarName,defaultBarVarName,defaultDualVarName,defaultSlackBarVarName,solutionType] translates the solutions of an optimization contained in a MOSEK JTASK file into a Mathematica association. The default variable and barvariable names are x and X; the default dual variable and dual barvariable names are y and Y. The default solution type is \"interior\" (\"basic\" and \"integer\") may also be possible.";


Begin["parseJTask`"]


(* ::Subsection::Closed:: *)
(*Helper functions*)


ClearAll[makeSparse];
makeSparse[<||>,dim_]:=SparseArray[{},dim/.Automatic->0];
makeSparse[l_List,dim_]:=makeSparse[Association@l,dim];
makeSparse[a_Association,{dim1_,dim2_}]:=SparseArray[Transpose[{a["subi"],a["subj"]}+1]->a["val"],{If[dim1===Automatic,Max[a["subi"]]+1,dim1],If[dim2===Automatic,Max[a["subj"]+1],dim2]}];
makeSparse[a_Association,dim_Integer]:=SparseArray[Lookup[a,"subi",a["subj"]]+1->a["val"],dim];
makeSparse[x_,dims_List,Symmetric]:=With[{s=makeSparse[x,dims]},s+UpperTriangularize[Transpose[s],1]];
makeSparse[x_,dims_Integer,Symmetric]:=makeSparse[x,{dims,dims},Symmetric];


ClearAll[sMat];
sMat[lowertriangle_,scaling_:1/Sqrt[2]]:=With[{d=1/2 (-1+Sqrt[1+8 Length[lowertriangle]])},
If[IntegerQ[d],
With[{m=Transpose[(PadLeft[Prepend[scaling Rest[#],First[#]],d,0]&)/@TakeList[lowertriangle,Range[d,1,-1]]]},
m+Transpose[LowerTriangularize[m,-1]]
],
Message[parseJTask::smatdim,Length[lowertriangle],Floor[d](Floor[d]+1)/2,Floor[d],Ceiling[d](Ceiling[d]+1)/2,Ceiling[d]]
]
]
parseJTask::smatdim="Dimension `1` of smat cone is not valid for a square matrix. Next appropriate dimensions are `2` (`3` \[Times] `3`) or `4` (`5` \[Times] `5`)";


ClearAll[getSparse];
getSparse[coefficients_,sparsematrices_,barvar_,MatrixStore_,barvariables_]/;Length[coefficients]===Length[sparsematrices]:=With[{spm=SparseArray[coefficients . MatrixStore[[sparsematrices+1]]],bm=barvariables[[barvar+1]]},
Module[{r},Sum[r[[2]]Indexed[bm,ReverseSort@r[[1]]],{r,Most@ArrayRules@spm}]]
]


(* ::Subsection::Closed:: *)
(*Boundary types*)


parseJTask$parsebound["lo",x_,lo_,_]:=x>=lo;
parseJTask$parsebound["up",x_,_,hi_]:=x<=hi;
parseJTask$parsebound["fx",x_,val_,val_]:=x==val;
parseJTask$parsebound["fx",x_,lo_,hi_]:=Message[parseJTask::bkfx,lo,hi,x];
parseJTask$parsebound["fr",x_,_,_]:=True;
parseJTask$parsebound["ra",x_,lo_,hi_]:=lo<=x<=hi;
parseJTask$parsebound[key_,x_,_,_]:=Message[parseJTask::unknownBk,key,x];


parseJTask::bkfx="Fixed bound keys requires lower bound `1` and upper bound `2` to coincide for expression `3`";
parseJTask::unknownBk="Variable bound key `1` for expression `2` unknown";


(* ::Subsection::Closed:: *)
(*Variable types*)


parseJTask$parsetype["cont",var_]:=True;
parseJTask$parsetype["int",var_]:=var\[Element]Integers;
parseJTask$parsetype[type_,var_]:=Message[parseJTask::unknownVt,type,var];


parseJTask::unknownVt="Variable type `1` for variable `2` unknown";


(* ::Subsection::Closed:: *)
(*Cone types*)


parseJTask$parsecone["zero",items_,_,_]:=items==0;
parseJTask$parsecone["rplus",items_,_,_]:=items\[VectorGreaterEqual]0;
parseJTask$parsecone["rminus",items_,_,_]:=items\[VectorLessEqual]0;
parseJTask$parsecone["r",items_,_,_]:=True;
parseJTask$parsecone["quad",items_,_,True]:=VectorGreaterEqual[{RotateLeft[items],0},"NormCone"];
parseJTask$parsecone["quad",items_,_,False]:=items[[1]]>=Sqrt[Total[Rest[items]^2]];
parseJTask$parsecone["rquad",items_,_,_]:=2items[[1]]items[[2]]>=Total[items[[3;;]]^2]&&items[[1]]>=0&&items[[2]]>=0;
parseJTask$parsecone["pexp",{a_,b_,c_},_,True]:=VectorGreaterEqual[{{c,b,a},0},"ExponentialCone"];
parseJTask$parsecone["pexp",{a_,b_,c_},_,False]:=a>=b E^(c/b)&&a>=0&&b>=0;
parseJTask$parsecone["pexp",items_,_,_]:=Message[parseJTask::conedim,"pexp",3,Length@items];
parseJTask$parsecone["dexp",{a_,b_,c_},_,True]:=VectorGreaterEqual[{{c,b,a},0},"DualExponentialCone"];
parseJTask$parsecone["dexp",{a_,b_,c_},_,False]:=a>=-c E^(b/c-1)&&a>=0&&c<=0;
parseJTask$parsecone["dexp",items_,_,_]:=Message[parseJTask::conedim,"dexp",3,Length@items];
parseJTask$parsecone["ppow",items_,{\[Alpha]_,_},True]:=VectorGreaterEqual[{items,0},{"PowerCone",\[Alpha]}];
parseJTask$parsecone["ppow",items_,\[Alpha]_,_]/;Length[\[Alpha]]<Length[items]:=With[{nl=Length@\[Alpha]},Times@@(items[[;;nl]]^\[Alpha])>=Sqrt[Total[items[[nl+1;;]]^2]]&&And@@Thread[items[[;;nl]]>=0]];
parseJTask$parsecone["ppow",items_,\[Alpha]_,_]:=Message[parseJTask::conedim,"ppow",Length@items,Length@\[Alpha]];
parseJTask$parsecone["dpow",items_,{\[Alpha]_,_},True]:=VectorGreaterEqual[{items,0},{"DualPowerCone",\[Alpha]}];
parseJTask$parsecone["dpow",items_,\[Alpha]_,_]/;Length[\[Alpha]]<Length[items]:=With[{nl=Length@\[Alpha]},Times@@((items[[;;nl]]/\[Alpha])^\[Alpha])>=Sqrt[Total[items[[nl+1;;]]^2]]&&And@@Thread[items[[;;nl]]>=0]];
parseJTask$parsecone["ppow",items_,\[Alpha]_,_]:=Message[parseJTask::conedim,"dpow",Length@items,Length@\[Alpha]];
parseJTask$parsecone["pgeom",items_,_,_]:=Power[Times@@Most[items], (Length[items]-1)^-1]>=Abs[Last[items]]&&And@@Thread[Most[items]>=0];
parseJTask$parsecone["dgeom",items_,_,_]:=(Length[items]-1)Power[Times@@Most[items], (Length[items]-1)^-1]>=Abs[Last[items]]&&And@@Thread[Most[items]>=0];
parseJTask$parsecone["svecpsd",items_,_,_]:=VectorGreaterEqual[{sMat[items],0},"SemidefiniteCone"];
parseJTask$parsecone[cone_,_,_,_]:=Message[parseJTask::conetype,cone];


parseJTask::conetype="Cone type `1` unknown";
parseJTask::conedim="Cone of type `1` must have dimension `2`, got `3`";


(* ::Subsection::Closed:: *)
(*Working on the individual parts*)


parseJTask$varbounds[var_,variables_]:=If[KeyExistsQ[var,"bk"],
Sow[parseJTask$parsebound@@#]&/@Transpose[{var["bk"],variables,var["bl"],var["bu"]}];
]


parseJTask$vartypes[var_,variables_]:=If[KeyExistsQ[var,"type"],
Sow[parseJTask$parsetype@@#]&/@Transpose[{var["type"],variables}]
];


parseJTask$ordconstr[con_,A_,bara_,Q_,variables_,MatrixStore_,barvariables_]:=If[KeyExistsQ[con,"bk"],
Module[{tmp=ConstantArray[0,Length[con["bk"]]]},
(* Linear constraints with normal variables *)
tmp+=makeSparse[Association[A],{Length@tmp,Length@variables}] . variables;
(* Linear constraints with PSD variables *)
(it|->tmp[[it[[1]]+1]]+=getSparse[it[[3]],it[[4]],it[[2]],MatrixStore,barvariables])/@bara;
(* Quadratic parts in constraints *)
(it|->tmp[[it[[1]]+1]]+=variables . makeSparse[<|"subi"->it[[2]],"subj"->it[[3]],"val"->it[[4]]|>,Length@variables,Symmetric] . variables)/@Q;
(* Boundaries of the constraints *)
Sow[parseJTask$parsebound@@#]&/@Transpose[{con["bk"],tmp,con["bl"],con["bu"]}];
]
]


parseJTask$newconic[AFE_,ACC_,domains_,variables_,MatrixStore_,barvariables_,conic_]:=If[KeyExistsQ[AFE,"numafe"],
Module[{tmp},
tmp=If[KeyExistsQ[AFE,"F"],
makeSparse[AFE["F"],{AFE["numafe"],Length@variables}] . variables,
ConstantArray[0,AFE["numafe"]]
];
If[KeyExistsQ[AFE,"g"],
tmp+=makeSparse[AFE["g"],AFE["numafe"]]
];
If[KeyExistsQ[AFE,"barf"],
(it|->tmp[[it[[1]]+1]]+=getSparse[it[[3]],it[[4]],it[[2]],MatrixStore,barvariables])/@AFE["barf"]
];
(it|->With[{dom=domains["type"][[it[[1]]+1]]},
Sow[parseJTask$parsecone[dom[[1]],tmp[[it[[2]]+1]]-it[[3]],dom[[2]],conic]];
])/@Transpose[{ACC["domain"],ACC["afeidx"],ACC["b"]}];
]
]


parseJTask$oldconic[qcone_,variables_,conic_]:=If[KeyExistsQ[qcone,"type"],
(it|->Sow[parseJTask$parsecone[it[[1]],variables[[it[[3]]+1]],it[[2]],conic]])/@Transpose[{qcone["type"],qcone["par"],qcone["members"]}];
]


(* ::Subsection::Closed:: *)
(*Function definition: parseJTask*)


parseJTask[file_,conic_:False,defaultVarName_:Global`x,defaultBarVarName_:Global`X]:=
With[{cmuopt=SystemOptions["CheckMachineUnderflow"]},
Internal`WithLocalSettings[
SetSystemOptions["CheckMachineUnderflow"->False],
With[{data=Association@Association[Import[file,"JSON"]]["Task/data"]},
With[{
var=Association[Lookup[data,"var",{}]],
barvar=Association[Lookup[data,"barvar",{}]],
objective=Association[Lookup[data,"objective",{}]],
MatrixStore=With[{sp=SparseArray[Transpose[#[[{2,3}]]+1]->#[[4]],ConstantArray[#[[1]],2]]},sp+UpperTriangularize[Transpose[sp],1]]&/@Lookup[data,"MatrixStore",{}]
},
With[{variables=MapIndexed[If[#1==="",Indexed[defaultVarName,#2[[1]]],Symbol[#1]]&,Lookup[var,"name",{}]],
barvariables=MapIndexed[If[#1==="",Indexed[defaultBarVarName,#2[[1]]],Symbol[#1]]\[Element]Matrices[ConstantArray[Extract[barvar["dim"],#2],2],Reals,Symmetric[{1,2}]]&,Lookup[barvar,"name",{}]]},
With[{conditions=Reap[
Sow[VectorGreaterEqual[{#1,0},"SemidefiniteCone"]]&/@barvariables[[All,1]];
parseJTask$varbounds[var,variables];
parseJTask$vartypes[var,variables];
parseJTask$ordconstr[
Association[Lookup[data,"con",{}]],
Association[Lookup[data,"A",{}]],
Lookup[data,"bara",{}],
Lookup[data,"Q",{}],
variables,
MatrixStore,
barvariables[[All,1]]
];
parseJTask$newconic[
Association[Lookup[data,"AFE",{}]],
Association[Lookup[data,"ACC",{}]],
Association[Lookup[data,"domains",{}]],
variables,
MatrixStore,
barvariables[[All,1]],
conic
];
If[Length[Association[Lookup[data,"DJC",{}]]]!=0,Message[parseJTask::djc]];
parseJTask$oldconic[
Association@Lookup[data,"qcone",{}],
variables,
conic
];
][[2,1]]},
If[objective["sense"]==="min",Inactive[Minimize],Inactive[Maximize]][
If[KeyExistsQ[objective,"c"],makeSparse[objective["c"],Length@variables] . variables,0]+
Lookup[objective,"cfix",0]+
If[KeyExistsQ[objective,"Q"],variables . makeSparse[objective["Q"],Length@variables,Symmetric] . variables,0]+
If[KeyExistsQ[objective,"barc"],Total[getSparse[#[[2]],#[[3]],#[[1]],MatrixStore,barvariables[[All,1]]]&/@objective["barc"]],0],
And@@conditions,
Join[variables,barvariables]
]
]
]
]
],
SetSystemOptions[cmuopt]
]
]


parseJTask::djc="Disjunctive constraints unsupported at the moment";


(* ::Subsection::Closed:: *)
(*Function definition: parseJTaskSolution*)


parseJTaskSolution[file_,defaultVarName_:Global`x,defaultBarVarName_:Global`X,defaultDualVarName_:Global`y,defaultSlackBarVarName_:Global`S,solutionType_:"interior"]:=
With[{cmuopt=SystemOptions["CheckMachineUnderflow"]},
Internal`WithLocalSettings[
SetSystemOptions["CheckMachineUnderflow"->False],
With[{alldata=Association[Import[file,"JSON"]]},
With[{problemdata=Association@alldata["Task/data"],solutiondata=Association@Association[alldata["Task/solutions"]][solutionType]},
Module[{variables,barvariables,normalduals,accduals,barslacks},
variables=MapIndexed[If[#1==="",Indexed[defaultVarName,#2[[1]]],Symbol[#1]]&,Lookup[Association@Lookup[problemdata,"var",{}],"name",{}]];
barvariables=MapIndexed[If[#1==="",Indexed[defaultBarVarName,#2[[1]]],Symbol[#1]]&,Lookup[Association@Lookup[problemdata,"barvar",{}],"name",{}]];
normalduals=MapIndexed[If[#1==="",Indexed[defaultDualVarName,#2[[1]]],Symbol[#1]]&,Lookup[Association@Lookup[problemdata,"con",{}],"name",{}]];
accduals=MapIndexed[If[#1==="",Indexed[defaultDualVarName,#2[[1]]+Length@normalduals],Symbol[#1]]&,Lookup[Association@Lookup[problemdata,"ACC",{}],"name",{}]];
barslacks=MapIndexed[If[#1==="",Indexed[defaultSlackBarVarName,#2[[1]]],Symbol[#1]']&,Lookup[Association@Lookup[problemdata,"barvar",{}],"name",{}]];
<|
"problemStatus"->solutiondata["prosta"],
"solutionStatus"->solutiondata["solsta"],
Sequence@@(Rule@@@Transpose[{variables,solutiondata["xx"]}]),
Sequence@@(Rule@@@Transpose[{barvariables,sMat[#,1]&/@solutiondata["barx"]}]),
Sequence@@(Rule@@@Transpose[{normalduals,solutiondata["y"]}]),
Sequence@@(Rule@@@Transpose[{accduals,solutiondata["doty"]}]),
Sequence@@(Rule@@@Transpose[{barslacks,sMat[#,1]&/@solutiondata["bars"]}])
|>
]
]
],
SetSystemOptions[cmuopt]
]
]


(* ::Subsection:: *)
(*End of package*)


End[]
