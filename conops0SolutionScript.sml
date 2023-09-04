(* conops0SolutionTheory *)
(* Author: Abhishek Parekh *)
(* Include required modules and open necessary theories *)
structure conops0SolutionTheory = struct

open HolKernel boolLib Parse bossLib
open acl_infRules aclrulesTheory aclDrulesTheory example1Theory

(***********
* create a new theory
***********)
val _ = new_theory "conops0SolutionTheory";

(************************************************************)
(* define the new datatypes, people and roles *)
(************************************************************)
(* Task 14.4.1 Task A *)

val _ =
Datatype
`commands = go | nogo | launch | abort | activate | stand_down`

val _ =
Datatype
`people = Alice | Bob`

val _ =
Datatype
`roles = Commander | Operator | CA`

(* KeyPrinc definition as provided *)
val keyPrinc =
Datatype
`keyPrinc = Staff conops0Solution$people
           | Role conops0Solution$roles
           | Ap num`

val _ = 
Datatype
`principals = PR keyPrinc | Key keyPrinc`

(* Task 14.4.1 Task B *)
(******************************************************)
(* Define cryptographic keys                          *)
(******************************************************)
val _ =
Datatype
`keys = KeyAlice | KeyBob | KeyCA`

(* OpRuleLaunch *)
val OpRuleLaunch_thm =
let
 val th1 = ACL_ASSUM``((Name Alice) says (prop go)):(commands,staff,'d,'e)Form``;
 val th2 = ACL_ASSUM``KeyAlice verifies (Name Alice says (prop go))``;
 val th3 = CONTROLS th1 th2;
 val th4 = DISCH(hd(hyp th2)) th3;
in
 DISCH(hd(hyp th1)) th4
end;

val _ = save_thm("OpRuleLaunch_thm",OpRuleLaunch_thm)


(* OpRuleAbort *)
val OpRuleAbort_thm =
let
 val th1 = ACL_ASSUM``((Name Bob) says (prop abort)):(commands,staff,'d,'e)Form``;
 val th2 = ACL_ASSUM``KeyBob verifies (Name Bob says (prop abort))``;
 val th3 = CONTROLS th1 th2;
 val th4 = DISCH(hd(hyp th2)) th3;
in
 DISCH(hd(hyp th1)) th4
end;

val _ = save_thm("OpRuleAbort_thm",OpRuleAbort_thm)


(* ApRuleActivate *)
val ApRuleActivate_thm =
let
 val th1 = ACL_ASSUM``((Name App) receives (prop activate))``;
 val th2 = SAYS ``(Name App)`` th1;
in
 DISCH(hd(hyp th1)) th2
end;

val _ = save_thm("ApRuleActivate_thm",ApRuleActivate_thm)


(* ApRuleStandDown *)
val ApRuleStandDown_thm =
let
 val th1 = ACL_ASSUM``((Name App) receives (prop stand down))``;
 val th2 = SAYS ``(Name App)`` th1;
in
 DISCH(hd(hyp th1)) th2
end;

val _ = save_thm("ApRuleStandDown_thm",ApRuleStandDown_thm)


(* Task 14.4.1 Task C *)

(* datatypes *)
val _ = Datatype `commands = go | nogo | launch | abort`;
val _ = Datatype `staff = Alice | Bob`;

(* OpRuleAbort_thm: Theorem for Operators issuing an abort command *)
val OpRuleAbort_thm =
TAC_PROOF(([],
``((M :(commands, 'b, staff, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
   Name (Key (Staff Bob)) quoting Name (PR (Role Operator)) says (prop abort) ==>
  (M,Oi,Os) sat (prop abort) impf (prop nogo)``),
REPEAT STRIP_TAC THEN
ACL_CONTROLS_TAC ``Name (Key (Staff Bob))`` THEN
ASM_REWRITE_TAC[]);

val _ = save_thm("OpRuleAbort_thm", OpRuleAbort_thm);


(* ApRuleActivate_thm: Theorem for Applications activating *)
val ApRuleActivate_thm =
TAC_PROOF(([],
``((M :(commands, 'b, staff, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
   Name (PR (Role Application)) says (prop activate) ==>
  (M,Oi,Os) sat Name (PR (Role Application)) controls (prop activate) ==>
  (M,Oi,Os) sat (prop activate)``),
REPEAT STRIP_TAC THEN
ACL_CONTROLS_TAC ``Name (PR (Role Application))`` THEN
ASM_REWRITE_TAC[]);

val _ = save_thm("ApRuleActivate_thm", ApRuleActivate_thm);


(* ApRuleStandDown_thm: Theorem for Applications standing down *)
val ApRuleStandDown_thm =
TAC_PROOF(([],
``((M :(commands, 'b, staff, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
   Name (PR (Role Application)) says (prop standdown) ==>
  (M,Oi,Os) sat Name (PR (Role Application)) controls (prop standdown) ==>
  (M,Oi,Os) sat (prop standdown)``),
REPEAT STRIP_TAC THEN
ACL_CONTROLS_TAC ``Name (PR (Role Application))`` THEN
ASM_REWRITE_TAC[]);

val _ = save_thm("ApRuleStandDown_thm", ApRuleStandDown_thm);



(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end (* structure *)
