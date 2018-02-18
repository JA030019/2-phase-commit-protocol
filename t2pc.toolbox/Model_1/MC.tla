---- MODULE MC ----
EXTENDS t2pc, TLC

\* CONSTANT definitions @modelParameterConstants:0RMMAYFAIL
const_151249093040485000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:1TMMAYFAIL
const_151249093040486000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2RM
const_151249093040487000 == 
{1,2,3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_151249093040488000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_151249093040489000 ==
Termination
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_151249093040490000 ==
Consistency
----
=============================================================================
\* Modification History
\* Created Tue Dec 05 11:22:10 EST 2017 by xinboyu
