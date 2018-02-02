# 2-phase-commit-protocol
In a distributed system, a transaction is performed by a collection of pro- cesses called resource managers (RMs), each executing on a different node. The transaction ends when the transaction manager (TM) issues a request either to commit or to abort the transaction. For the transaction to be com- mitted, each participating RM must be willing to commit it. Otherwise, the transaction must be aborted. Prior to the commit request, any RM may spontaneously decide to abort its part of the transaction. The fundamental requirement is that all RMs must eventually agree on whether the transaction is committed or aborted. (https://www.microsoft.com/en-us/research/ wp-content/uploads/2016/02/tr-2003-96.pdf)

Below find a model of 2-phase commit. (This was built by modifying the P2TCommit.tla at http://lamport.azurewebsites.net/tla/two-phase. html to add a TM agent). We will start with that code as the basis for what comes next.

If no faults occur, the 2-phase commit algorithm is correct. In the pres- ence of a crash fault, however, problems can arise. In the questions below, we will use TLA+/PlusCal to explore what problems may arise, and how to properly design the protocol to overcome those problems.

