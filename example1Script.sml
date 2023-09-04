(* example1Theory *)
(* Author: Abhishek Parekh *)

structure example1Script = struct

open HolKernel boolLib Parse bossLib
open acl_infRules aclrulesTheory aclDrulesTheory 

(***********
* create a new theory
***********)
val _ = new_theory "example1Theory";


(* Define some names of people who will be principals *)
(******************************************************)
val _ =
Datatype
`staff = Alice | Bob`


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



val aclExercise1 =
let
 val th1 = ACL_ASSUM "(Name Alice says prop go):(commands,        staff, 'd, 'e)Form" 
 val th2 = ACL_ASSUM "(Name Bob says prop go):(commands, staff,          'd, 'e)Form"
 val th3 = ACL_CONJ th1 th2
 val th4 = AND_SAYS_RL th3
 val th5 = DISCH (hd (hyp th2)) th4
in
 DISCH (hd (hyp th1)) th5
end;

(* Save the theorem *)
val _ = save_thm("aclExercise1", aclExercise1)



(*******************)
(* aclExercise1A proof *)
(*******************)

val aclExercise1ATheorem = 
TAC_PROOF(([],
"((M,Oi,Os) sat (Name Alice says prop go)) ==>
  ((M,Oi,Os) sat (Name Bob says prop go)) ==>
  ((M,Oi,Os) sat (Name Alice meet Name Bob says prop go))"),
PROVE_TAC[Meet, Says, Controls])

val _ = save_thm("aclExercise1ATheorem", aclExercise1ATheorem)


(*********************************)
(* aclExercise1B proof *)
(*********************************)

val aclExercise1BTheorem = 
TAC_PROOF(([],
``((M :(commands, 'b, staff, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
   (Name Alice says prop go) ==>
  (M,Oi,Os) sat (Name Bob says prop go) ==>
  (M,Oi,Os) sat ((Name Alice meet Name Bob) says prop go)``),
PROVE_TAC[ACL_CONJ_TAC, ACL_AND_SAYS_RL_TAC, ASM_REWRITE_TAC[]])

val _ = save_thm("aclExercise1BTheorem", aclExercise1BTheorem)




(* Prove the desired theorem *)
val aclExercise2 =
let
  val th1 = ACL_ASSUM ``((M,Oi,Os) sat Name Alice says prop go):('a,'b,'c,'d)Form``;
  val th2 = ACL_ASSUM ``((M,Oi,Os) sat Name Alice controls prop go):('a,'b,'c,'d)Form``;
  val th3 = ACL_ASSUM ``((M,Oi,Os) sat prop go impf prop launch):('a,'b,'c,'d)Form``;
  val th4 = ACL_ASSUM ``((M,Oi,Os) sat Name Bob says prop launch):('a,'b,'c,'d)Form``;

  val th5 = CONTROLS th2 th1;
  val th6 = ACL_MP th5 th3;

in
  DISCH (hd (hyp th1)) (DISCH (hd (hyp th2)) (DISCH (hd (hyp th3)) th4))
end;

(* Save the theorem *)
val _ = save_thm ("aclExercise2", aclExercise2);


(***************************************************)
(* Exercise 13.10.2 Task B                         *)
(***************************************************)

(* Goal-oriented proof for aclExercise2A *)
val aclExercise2A =
TAC_PROOF(([],
“((M : ‘a, ‘b, ‘c, ‘d) Kripke),(Oi :’d po),(Os :'e po)) sat 
    Name Alice says (prop go) ==>
    (M,Oi,Os) sat Name Alice controls (prop go) ==>
    (M,Oi,Os) sat (prop go impf prop launch) ==>
    (M,Oi,Os) sat Name Bob says (prop launch)``),
PROVE_TAC[Modus_Ponens, Controls, Says])

(* Save the theorem *)
val _ = save_thm("aclExercise2A", aclExercise2A)



(***************************************************)
(* Exercise 13.10.2 Task C                         *)
(***************************************************)
(* A goal-oriented proof using tactics *)
val aclExercise2B =
TAC_PROOF(([],
``((M :(commands, 'b, staff, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
   Name Alice says (prop go) ==>
  (M,Oi,Os) sat Name Alice controls (prop go) ==>
  (M,Oi,Os) sat (prop go) impf (prop launch) ==>
  (M,Oi,Os) sat Name Bob says (prop launch)``),
REPEAT STRIP_TAC THEN 
ACL_CONTROLS_TAC ``Name Alice`` THEN 
ASM_REWRITE_TAC[] THEN
PAT_ASSUM 
``(M,Oi,Os) sat (prop go) impf (prop launch)``
(fn th1 => 
 (PAT_ASSUM 
  ``(M,Oi,Os) sat (prop go)``
  (fn th2 => ASSUME_TAC(ACL_MP th2 th1)))) THEN 
ASM_REWRITE_TAC[] THEN
SAYS_TAC ``(Name Bob):staff Princ``)

val _ = save_thm("aclExercise2B",aclExercise2B)



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



(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end (* structure *)