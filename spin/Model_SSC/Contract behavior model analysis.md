Based on the SSC model, reasonable parameters are set for the contract, and the model is simulated and the contract function attributes are detected.As shown in Figure 21, a simple simulation of information interaction for Merchant Process Merchant, Customer Process Customer, and Contract Account Process Contract.


![Figure 21 Simple simulation of SSC 3process communication](https://i.imgur.com/3EmNfn3.jpg "Figure 21 Simple simulation of SSC 3process communicatio")


The following is a partial code for the SSC model function detection. As shown in Table 29, the process for the SSC model client represents the client state machine in the smart contract. In the process Customer, the local variables and processes representing the state of the process are defined. In the initial state, etc., the interaction with the merchant process Merchant is given in the proce.


![Table 29 The main code of the Customer process in the SSC model](https://i.imgur.com/BD7KHTO.jpg "Table 29 The main code of the Customer process in the SSC model")


![Table 30 Main code of the Merchant process in the SSC model](https://i.imgur.com/xAg4cDW.jpg "Table 30 Main code of the Merchant process in the SSC model")


As shown in Table 30, the merchant process for the SSC model represents the merchant state machine in the smart contract. In the process Merchant, the local state of the process and the initial state of the process are defined, and the initial process is written into the message channel, so that other processes can read the state of the process. The interaction with the customer process Customer and the contract account process Contract is also defined in the process Merchant.

Figure 22 shows the error termination simulation for multi-process interaction in the SSC model. The error is caused by a wrong transition condition of the state during the running of the model, which causes the model to end the simulation execution of the model in the contract book process.


![Figure 22 Error termination simulation of SSC process interaction](https://i.imgur.com/m42aztv.jpg "Figure 22 Error termination simulation of SSC process interaction")


Figure 23 shows the correct simulation of process interaction in the SSC model. The process in the first column is the process of init(), which is the startup process of the entire model, and the second column is the process of Customer(). The process number is 1, third. Listed as the Merchant() process, the process number is 2, the fourth column is the Contract() process, the process number is 3, and the process number is encoded in the order of startup, which is the unique identifier of the process in the model. The arrow pointing to the red line in the figure indicates the interaction between processes, and the red line is next to the description of this interaction, which is defined in the SSC model.


![Figure 23 Correct trajectory of SSC process interaction](https://i.imgur.com/IEwi5Kh.jpg "Figure 23 Correct trajectory of SSC process interaction")


Table 31 shows the changes in SSC processes and variables, and the communication status when XSPIN generates the smart contract PROMELA model. Only the execution of some processes is listed. Table 32 describes a partial time series in which the SSC process runs. Figure 24 shows the balance of each process account after the contract execution is completed. All accounts in the SSC must be consistent, with detailed verification and instructions.


![Table 31 SSC model implementation](https://i.imgur.com/ShnVsLi.jpg "Table 31 SSC model implementation")


![Table 32 Time series of SSC model execution](https://i.imgur.com/T0e57k1.jpg "Table 32 Time series of SSC model execution")


![Figure 24 Data values after the SSC model is executed](https://i.imgur.com/4sVpULP.jpg "Figure 24 Data values after the SSC model is executed")
