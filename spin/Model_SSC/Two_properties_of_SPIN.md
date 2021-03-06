                                                    
#  Verifiable functional properties of SPIN

In the model detection process of SPIN, verification of functional properties is the basis for the correctness of the contract, ensuring that the smart contract implements the function and then verifying whether the smart contract satisfies the nature constraint.
	
For the SSC mentioned in the article, the contract functions that need to be tested include: Can Merchant Merchant give correct feedback when Customer Customer initiates a shopping request, and can Customer Customer pay for the goods when Merchant Merchant has sent the delivery message? Transfer to the contract account Contract and so on.
	

Only the contract can verify the other constraint properties of the contract based on the basic functions.
	
The verification of functional properties mainly includes two aspects: activity (liveness) verification and security (safety) verification. The activity of the system refers to the actions that must occur in the system, such as the termination of the contract (CFinal) state. The security attribute of the contract model refers to the contract without deadlock, that is, the system will not fall into any state that cannot trigger the execution under any conditions.
	
In SPIN, we can detect the assertion and invalid termination state of the SSC by selecting the assertion and envalid endstates options. For SPIN, the activity verification provided by the system mainly means that the contract model must reach the contractual termination (CFinal) state, and the execution of the process in the contract will trigger the contract to enter the next state, that is, if the contract enters the initial state ( CInit) state, then the contract will eventually reach the CFinal state.
	
SPIN confirms whether the contract is in a livelock state by detecting infinite loops and no progress. Similarly, it is detected whether the contract is deadlock by detecting the invalid end state of the contract. SPIN offers three activity detection options: non-progress cycle, Acceptance cycles, and weak fairness.

# Verifiable non-functional properties of SPIN                                
	
A smart contract can be intuitively understood as a multi-party agreement between multiple contract parties. Therefore, the verification of a smart contract system includes two aspects: 

(1) the functionals properties of the smart contract, that is, the behavior of the smart contract;

(2) The non-functional properties of the smart contract, that is, the nature constraint of the smart contract. 
	
For smart contracts, different contract templates have different requirements for functional properties, and non-functional properties are quite different.
	
For the SSC model of the modeling and verification system in this paper, the contract commodity is atomic, and in the process of contract transaction, the transfer amount is also atomic.
	
Therefore, because of the transactions involved in the contract, such as transfer or payment, the atomicity of goods and accounts is the first important attribute to be verified.
	
In addition, in smart contracts, the account balances of multiple contractor accounts and contract accounts must be consistent, so consistency is another important attribute that needs to be verified in the SSC.
