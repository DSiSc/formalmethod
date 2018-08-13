# Formal Methods
Demo of Formal Methods of Smart Contracts

## e-shopping smart contract
**e-shopping.pml is a simple e-shopping contract program build by PROMELA, and we verify this contract by iSpin.**

Detail Process:
1. build e-shopping contract program
2. install iSpin follow the guide of [How to install iSpin](http://spinroot.com/spin/Man/README.html "Install Guide")
3. use iSpin to verify our contract program（[Using iSpin](http://spinroot.com/spin/Man/3_SpinGUI.html "Using iSpin")）
    * ispin e-shopping.pml
    * click 'Syntax Check'： check our program
    * click 'Simulate/Replay' -> (Re)Run： run check
    * result dialog will show the check result
4. finally, our check result was recorded in 'result.png'