(* documentation.sml                                    *)
(* We need to load the HOL theories we want to print out *)

app 
 load 
 ["conops0SolutionTheory","solutions1Theory","example1Theory","aclrulesTheory","aclDrulesTheory","EmitTeX"];

load "conops0SolutionTheory";
load "solutions1Theory";
load "example1Theory";
open EmitTeX;


print_theories_as_tex_doc
["conops0SolutionTheory"] "conops0SolutionTheoryReport";
["solutions1Theory"] "solutions1TheoryReport";
["example1Theory"] "example1TheoryReport";
