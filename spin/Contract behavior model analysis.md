<html>

<head>
<meta http-equiv=Content-Type content="text/html; charset=gb2312">
<meta name=Generator content="Microsoft Word 15 (filtered)">
<style>
<!--
 /* Font Definitions */
 @font-face
	{font-family:"Cambria Math";
	panose-1:2 4 5 3 5 4 6 3 2 4;}
@font-face
	{font-family:等线;
	panose-1:2 1 6 0 3 1 1 1 1 1;}
@font-face
	{font-family:"\@等线";
	panose-1:2 1 6 0 3 1 1 1 1 1;}
 /* Style Definitions */
 p.MsoNormal, li.MsoNormal, div.MsoNormal
	{margin:0cm;
	margin-bottom:.0001pt;
	text-align:justify;
	text-justify:inter-ideograph;
	font-size:10.5pt;
	font-family:等线;}
.MsoChpDefault
	{font-family:等线;}
 /* Page Definitions */
 @page WordSection1
	{size:595.3pt 841.9pt;
	margin:72.0pt 90.0pt 72.0pt 90.0pt;
	layout-grid:15.6pt;}
div.WordSection1
	{page:WordSection1;}
-->
</style>

</head>

<body lang=ZH-CN style='text-justify-trim:punctuation'>

<div class=WordSection1 style='layout-grid:15.6pt'>

<p class=MsoNormal>

<table cellpadding=0 cellspacing=0>
 <tr>
  <td width=69 height=0></td>
 </tr>
 <tr>
  <td></td>
  <td><img width=406 height=428
  src="Contract%20behavior%20model%20analysis.files/image001.jpg"></td>
 </tr>
</table>

<br clear=ALL>
<span lang=EN-US>Based on the SSC model, reasonable parameters are set for the
contract, and the model is simulated and the contract function attributes are
detected.As shown in Figure 21, a simple simulation of information interaction
for Merchant Process Merchant, Customer Process Customer, and Contract Account
Process Contract.</span></p>

<p class=MsoNormal><span lang=EN-US>&nbsp;</span></p>

<p class=MsoNormal><img width=434 height=249
src="Contract%20behavior%20model%20analysis.files/image002.jpg"><br clear=ALL>
<span lang=EN-US>The following is a partial code for the SSC model function
detection. As shown in Table 29, the process for the SSC model client
represents the client state machine in the smart contract. In the process
Customer, the local variables and processes representing the state of the
process are defined. In the initial state, etc., the interaction with the
merchant process Merchant is given in the process.</span></p>

<p class=MsoNormal><span lang=EN-US>&nbsp;</span></p>

<p class=MsoNormal>

<table cellpadding=0 cellspacing=0 align=left>
 <tr>
  <td width=20 height=0></td>
 </tr>
 <tr>
  <td></td>
  <td><img width=534 height=462
  src="Contract%20behavior%20model%20analysis.files/image003.jpg"></td>
 </tr>
</table>

<br clear=ALL>
</p>

<p class=MsoNormal><span lang=EN-US>As shown in Table 30, the merchant process
for the SSC model represents the merchant state machine in the smart contract.
In the process Merchant, the local state of the process and the initial state
of the process are defined, and the initial process is written into the message
channel, so that other processes can read the state of the process. The
interaction with the customer process Customer and the contract account process
Contract is also defined in the process Merchant.</span></p>

<p class=MsoNormal><span lang=EN-US>Figure 22 shows the error termination
simulation for multi-process interaction in the SSC model. The error is caused
by a wrong transition condition of the state during the running of the model,
which causes the model to end the simulation execution of the model in the
contract book process.</span></p>

<p class=MsoNormal><span lang=EN-US><img width=400 height=222 id="图片 7"
src="Contract%20behavior%20model%20analysis.files/image004.jpg"></span></p>

<p class=MsoNormal><span lang=EN-US>Figure 23 shows the correct simulation of
process interaction in the SSC model. The process in the first column is the
process of init(), which is the startup process of the entire model, and the
second column is the process of Customer(). The process number is 1, third.
Listed as the Merchant() process, the process number is 2, the fourth column is
the Contract() process, the process number is 3, and the process number is
encoded in the order of startup, which is the unique identifier of the process
in the model. The arrow pointing to the red line in the figure indicates the
interaction between processes, and the red line is next to the description of
this interaction, which is defined in the SSC model.</span></p>

<p class=MsoNormal><span lang=EN-US><img width=441 height=688 id="图片 8"
src="Contract%20behavior%20model%20analysis.files/image005.jpg"></span></p>

<p class=MsoNormal><span lang=EN-US>&nbsp;</span></p>

<p class=MsoNormal><span lang=EN-US>&nbsp;</span></p>

<p class=MsoNormal><span lang=EN-US>Table 31 shows the changes in SSC processes
and variables, and the communication status when XSPIN generates the smart
contract PROMELA model. Only the execution of some processes is listed. Table
32 describes a partial time series in which the SSC process runs. Figure 24
shows the balance of each process account after the contract execution is
completed. All accounts in the SSC must be consistent, with detailed
verification and instructions.</span></p>

<p class=MsoNormal><span lang=EN-US><img width=554 height=197 id="图片 9"
src="Contract%20behavior%20model%20analysis.files/image006.jpg"><img width=554
height=275 id="图片 10"
src="Contract%20behavior%20model%20analysis.files/image007.jpg"><img width=308
height=135 id="图片 11"
src="Contract%20behavior%20model%20analysis.files/image008.jpg"></span></p>

</div>

</body>

</html>
