-------------------------------- MODULE t2pc --------------------------------
\** ZHENG KAI 50247576 **
\** XINBO YU  50102922 **
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM, RMMAYFAIL, TMMAYFAIL

(*
--algorithm t2pc {
    variable rmState = [rm \in RM |-> "working"];
             tmState = "init";
    define {
        canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"} 
        canAbort == \E rm \in RM :  rmState[rm] \in {"aborted", "failed"} /\ tmState # "committed"
    }
    
    macro Prepare(p) {
        await rmState[p] = "working";
              rmState[p] := "prepared";    
    }
   
    macro Decide(p) {        
        either { if (rmState[p] = "prepared" /\ tmState = "committed")
        {
                 rmState[p] := "committed"
                 }
        }                
        or { if (rmState[p] \in {"working"} \/ ((rmState[p] = "prepared") /\ (tmState = "aborted")))
        {
                 rmState[p] := "aborted"
                 }
        }
    }
    
    macro Fail(p) {
        if (RMMAYFAIL) {
            either rmState[p] := "failed"; 
            or skip;
        }
    }
   
    fair process (RManager \in RM) {
        RS: while (rmState[self] \in {"working", "prepared"}) { 
               either Prepare(self) or Decide(self) or Fail(self)
        }       
    }
    
    fair process(TManager = 0) {
        TS: either { await canCommit;
            TC: tmState := "committed";
            F1: if (TMMAYFAIL) tmState := "hidden";}
            
        or { await canAbort;
            TA: tmState := "aborted";
            F2: if (TMMAYFAIL) tmState := "hidden";}
    }
    
    \* TM backup
    fair process(TManagerBackup = 1) {
        L1: await \/ TMMAYFAIL /\ tmState = "hidden" 
                  \/ ~TMMAYFAIL;
        if (tmState = "hidden") {
            TS: either {
                await canCommit;
                TC: tmState := "committed";
            }
            or {
                await canAbort;
                TA: tmState := "aborted";
            }
        }
    }
}
*)
\* BEGIN TRANSLATION
\* Label TS of process TManager at line 48 col 13 changed to TS_
\* Label TC of process TManager at line 49 col 17 changed to TC_
\* Label TA of process TManager at line 53 col 17 changed to TA_
VARIABLES rmState, tmState, pc

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
canAbort == \E rm \in RM :  rmState[rm] \in {"aborted", "failed"} /\ tmState # "committed"


vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0} \cup {1}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS_"
                                        [] self = 1 -> "L1"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ IF rmState[self] = "prepared" /\ tmState = "committed"
                                         THEN /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED rmState
                                \/ /\ IF rmState[self] \in {"working"} \/ ((rmState[self] = "prepared") /\ (tmState = "aborted"))
                                         THEN /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED rmState
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ \/ /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                           \/ /\ TRUE
                                              /\ UNCHANGED rmState
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

TS_ == /\ pc[0] = "TS_"
       /\ \/ /\ canCommit
             /\ pc' = [pc EXCEPT ![0] = "TC_"]
          \/ /\ canAbort
             /\ pc' = [pc EXCEPT ![0] = "TA_"]
       /\ UNCHANGED << rmState, tmState >>

TC_ == /\ pc[0] = "TC_"
       /\ tmState' = "committed"
       /\ pc' = [pc EXCEPT ![0] = "F1"]
       /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA_ == /\ pc[0] = "TA_"
       /\ tmState' = "aborted"
       /\ pc' = [pc EXCEPT ![0] = "F2"]
       /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS_ \/ TC_ \/ F1 \/ TA_ \/ F2

L1 == /\ pc[1] = "L1"
      /\ \/ TMMAYFAIL /\ tmState = "hidden"
         \/ ~TMMAYFAIL
      /\ IF tmState = "hidden"
            THEN /\ pc' = [pc EXCEPT ![1] = "TS"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << rmState, tmState >>

TS == /\ pc[1] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![1] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![1] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[1] = "TC"
      /\ tmState' = "committed"
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[1] = "TA"
      /\ tmState' = "aborted"
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED rmState

TManagerBackup == L1 \/ TS \/ TC \/ TA

Next == TManager \/ TManagerBackup
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(TManagerBackup)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-------------------------------------------------------------------------------------------
Termination2 == <>(\A self \in ProcSet: pc[self] = "Done")
Consistency == \A rm1, rm2 \in RM: ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
===========================================================================================
\** ZHENG KAI 50247576 **
\** XINBO YU  50102922 **
\* Part 1.1
\* Model check Consistency and Termination with RMMAYFAIL=FALSE and TMMAYFAIL=FALSE, 
\* it means that no RM fasle and no TM false, and there are no errors in my program.
\* Model check Consistency and Termination with RMMAYFAIL=TRUE and TMMAYFAIL=FALSE,
\* it means that RM can be fasle and no TM false, not all RMs can change their status to committed, and there are no errors in my program.

\* Part 1.2
\* Model check Consistency and Termination with RMMAYFAIL=FALSE and TMMAYFAIL=TRUE, 
\* it means that no RM fasle and TM will be false, and the Termination property will be violated.
\* The error example is rmState<"aborted", "prepared", "aborted"> and tmState = hidden. When
\* tmState equals hidden, it doesn't make a decison. When the RMs read the state of the TM, it can't 
\* return committed or aborted, so the RMs can't change their state.

\* Part 1.3
\* When set RMMAYFAIL TRUE and TMMAYFAIL TRUE, model check Consistency and Termination
\* Both of them are not violated. Because when TM fail, the RMs can connect to the Backup TM, 
\* they can read the state of Backup TM, the Backup TM can reset the status of the tm, so the RMs can 
\* change to their right final status according to tmState.

\* Modification History
\* Last modified Tue Dec 05 11:17:23 EST 2017 by xinboyu
\* Last modified Tue Nov 28 13:56:03 EST 2017 by kz-pc
\* Created Sun Nov 26 15:42:50 EST 2017 by xinboyu

