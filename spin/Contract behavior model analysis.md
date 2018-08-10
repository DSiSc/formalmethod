Based on the SSC model, reasonable parameters are set for the contract, and the model is simulated and the contract function attributes are detected.As shown in Figure 21, a simple simulation of information interaction for Merchant Process Merchant, Customer Process Customer, and Contract Account Process Contract.

![](https://i.imgur.com/Vb26DKc.jpg)

The following is a partial code for the SSC model function detection. As shown in Table 29, the process for the SSC model client represents the client state machine in the smart contract. In the process Customer, the local variables and processes representing the state of the process are defined. In the initial state, etc., the interaction with the merchant process Merchant is given in the proce.

![](https://i.imgur.com/yMoEuiU.jpg)

![](https://i.imgur.com/dXYlAHN.jpg)

As shown in Table 30, the merchant process for the SSC model represents the merchant state machine in the smart contract. In the process Merchant, the local state of the process and the initial state of the process are defined, and the initial process is written into the message channel, so that other processes can read the state of the process. The interaction with the customer process Customer and the contract account process Contract is also defined in the process Merchant.

Figure 22 shows the error termination simulation for multi-process interaction in the SSC model. The error is caused by a wrong transition condition of the state during the running of the model, which causes the model to end the simulation execution of the model in the contract book process.

![](https://i.imgur.com/IV6HqUm.jpg)

Figure 23 shows the correct simulation of process interaction in the SSC model. The process in the first column is the process of init(), which is the startup process of the entire model, and the second column is the process of Customer(). The process number is 1, third. Listed as the Merchant() process, the process number is 2, the fourth column is the Contract() process, the process number is 3, and the process number is encoded in the order of startup, which is the unique identifier of the process in the model. The arrow pointing to the red line in the figure indicates the interaction between processes, and the red line is next to the description of this interaction, which is defined in the SSC model.

![](https://i.imgur.com/AZJhcaO.jpg)

Table 31 shows the changes in SSC processes and variables, and the communication status when XSPIN generates the smart contract PROMELA model. Only the execution of some processes is listed. Table 32 describes a partial time series in which the SSC process runs. Figure 24 shows the balance of each process account after the contract execution is completed. All accounts in the SSC must be consistent, with detailed verification and instructions.

![](https://i.imgur.com/CasaaR5.jpg)

![](https://i.imgur.com/K2iaKDd.jpg)

![](https://i.imgur.com/5rhfW86.jpg)