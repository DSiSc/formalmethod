This example is a PROMELA version of an ancient algorithm for finding primes by counting off numbers and systematically intercepting the non-primes among them. The algorithm, a favorite programming exercise today, is due to the Greek philosopher and mathematician Eratosthenes of Cyrene (a city in modern day Libya which is today called Shahhat). Figure 1 shows a version in PROMELA that makes use of the fact that we can use dynamic process creation and pass channel identifiers between running processes.

Figure 1 The Sieve of Eratosthenes

```
 1 /*
 2     The Sieve of Eratosthenes (c. 276-196 BC)
 3     Prints all prime numbers up to MAX
 4 */
 5 #define MAX 25
 6
 7 mtype = { number, eof };
 8
 9 chan root = [0] of { mtype, int };
10
11 proctype sieve(chan c; int prime)
12 {    chan child = [0] of { mtype, int };
13      bool haschild;
14      int n;
15
16      printf("MSC: %d is prime\n", prime);
17 end: do
18      :: c?number(n) ->
19         if
20         :: (n%prime) == 0 ->
21            printf("MSC: %d = %d*%d\n", n, prime, n/prime)
22         :: else ->
23         if
24            :: !haschild -> /* new prime */
25                   haschild = true;
26                   runsieve(child, n);
27            :: else ->
28                   child!number(n)
29            fi;
30         fi
31      :: c?eof(0) ->
32         break
33      od;
34      if
35      :: haschild ->
36         child!eof(0)
37      :: else
38      fi
39 }
40
41 init
42 {   int n = 2;
43
44     run sieve(root, n);
45     do
46     :: (n < MAX) -> n++; root!number(n)
47     :: (n >= MAX) -> root!eof(0); break
48     od
49 }
```

Because a PROMELA model must always be finite, we have to place an upper-bound on the largest integer value that we will test for primality. SPIN is not designed to handle computational problems, so do not expect to get away with a very large bound here. The bound is defined in Figure 1 in a macro definition named MAX. We have used the value 25. Only two types of messages are used, defined in an mtype declaration, and named number and eof. The latter type of message is used to trigger an orderly termination of the system of processes when the test for primality of the number with the maximal value allowed has been completed.

Our system of processes starts off with just a single running process: init. The principle of operation of the algorithm is that we test integer numbers one by one, in ascending order. We will start off assuming that we know only that two is a prime. Clearly, for any higher number to be prime, it should minimally not be divisible by two, so the first thing that the initial process will do is to start up a tester for that value. The initial process does so by creating a first process of type sieve, and passing it in an argument the value two as a first prime number to use in the tests. Also passed is an argument is the name of the channel that the initial process will use to communicate further information to the sieve process. For the first process this is a globally declared rendezvous channel named root.

Once the first test process is set up, the initial process will simply pass all integer numbers greater than two, up to the preset maximum, to its newly created child. It is the child's job now to figure out if the numbers passed to it are prime, and it is free to create its own children to help do the job.

When a process of type sieve starts up, the first thing it will do is to acknowledge the fact that it was passed, what it trusts is, a prime number as an argument. It does so by printing the number (line 16 in Figure 1), using the prefix MSC: to make sure that this line of output will be picked up in the message sequence charts that can be created by XSPIN. Next, it stops and waits for input to arrive on the channel that was passed to it by its parent.

One of only two types of messages can arrive, as shown on line 18 and line 31 in Figure 1.

A message of type number carries an integer number that is to be tested for primality. Every single instantiation of the sieve process will test if the number is divisible by the prime number it was passed by its parent. If divisible, the number is not prime, and that fact is printed. Otherwise, the number is passed to the next process to test for possibly more known primes. If no next process exists yet, the value of local boolean variable haschild will still be false (the default initial value). The sieve process will now clone itself and start up a new copy of sieve, passing the newly discovered prime number as an argument, as well as the name of the local channel child that it will use to pass new numbers.

If a child process already exists, that means that more tests for primality have yet to be done before this new number can be declared prime. The number is simply sent to the child process over the local channel, and the test process is repeated.

Meanwhile, the initial process can be sending a new number into the pipeline of primality testers, and in principle all processes can be active simultaneously, each testing the divisibility of a different number against the prime number they each hold. A simulation run might proceed as follows:

![](https://i.imgur.com/ykDzzHG.jpg)


Although the algorithm itself is deterministic, the process scheduling is not, and in different runs this can cause print statements to appear in slightly different orders. Ten processes were created, one of which is the initial process. This means that the algorithm accurately found the nine prime numbers between one and 25. When the maximal number is reached, the eof messages is passed down the chain all the way from the initial process to the most recently created sieve process, and all processes will make an orderly exit.

A verification run with the model as specified is uneventful:

![](https://i.imgur.com/RPrs3Ry.jpg)


There are no deadlocks and there is no unreachable code, as we would expect. The partial order reduction algorithm could in principle work better, though, if we can provide some extra information about the way that the initial and the sieve processes access the message channels. In principle, this is not too hard in this case. On line 15, for instance, we can try to add the channel assertions



15 xr c; xs child;


because the sieve process is guaranteed to be the only process to read from the channel that was passed to it as an argument, and the only one to send messages to the channel it will use to communicate with a possible child process. Similarly, the assertion



43 xs root;


could be included on line 43 in the init process to assert that the initial process is the only process to send messages to channel root. If we do so, however, the verifier will warn us sternly that channel assertions are not allowed on rendezvous channels.

```
$ spin -a eratosthenes
$ cc -o pan pan.c
$ ./pan
chan root (0), sndr proc :init: (0)
pan: xs chans cannot be used for rv (at depth 0)
pan: wrote eratosthenes.trail
...
```


We can correct this by turning the two rendezvous channels declared on lines 9 and 12 in Figure 1 into buffered message channels with the minimum storage capacity of one message. Line 9 in Figure 1 then becomes:



9 chan root = [1] of { mtype, int };


Similarly, line 12 is now written:



12 { chan child = [1] of { mtype, int };


This of course in itself will increase the number of potentially reachable states, since it decouples the process executions a little more. Repeating the verification confirms this. If the channel assertions are not included, the number of reachable states now increases tenfold (to 24,548). With the channel assertions, however, the size of the state space decreases tenfold to a mere 289 reachable states, which provides a compelling illustration of the effectiveness of channel assertions.

In this first model we are using one process for each prime number that is found. Because there cannot be more than 255 running processes in a SPIN model, we cannot use this model to find more than only the first 254 prime numbers greater than one. This means that a value for MAX greater than 1,609 (the 254th prime) would be of little use, unless we can somehow rearrange the code to avoid the dynamic creation of processes. This is not too hard, as shown in Figure 2, though the resulting model is not quite as elegant.

Figure 2 Alternative Structure for Sieve

```
 1 mtype = { number, eof };
 2
 3 chan found = [MAX] of { int };
 4
 5 active proctype sieve()
 6 {  int n = 3;
 7    int prime = 2;
 8    int i;
 9
10    found!prime;
11    printf("MSC: %d is prime\n", prime);
12    do
13    :: n < MAX ->
14       i = len(found);
15       assert(i > 0);
16       do
17       :: i > 0 ->
18           found?prime;
19           found!prime; /* put back at end */
20           if
21           :: (n%prime) == 0 ->
22           /* printf("MSC: %d = %d*%d\n",
23                      n, prime, n/prime); */
24              break
25           :: else ->
26               i--
27           fi
28       :: else ->
29           break
30       od;
31       if
32       :: i == 0 ->
33           found!n;
34           printf("MSC: %d is prime number %d\n",
35                       n, len(found))
36       :: else
37       fi;
38       n++
39    :: else ->
40       break
41    od
42 }
```
        
This time we store prime numbers in a channel, and retrieve them from there for primality testing. We have set the capacity of the channel generously to the value of MAX, although a much smaller value would also suffice. Only a number that is not divisible by any of the previously discovered primes is itself prime and can then be added into the channel. In this version of the sieve process we have left the macro MAX undefined, which means that we can now pass a value in via a command-line argument to SPIN. We can now surpass the old limit of 254 primes easily, for instance, as follows:

![](https://i.imgur.com/X7Bdfg0.jpg)


If we repeat the verification attempt for the alternative model, using the same value for MAX as before, we see that the number of states has increased a little compared to the best attempt from before using channel assertions.

![](https://i.imgur.com/KSnCMM4.jpg)

However, we can also note that the size of the state vector has decreased from 284 bytes in the first model, which increases with MAX, to a fixed size of just 132 bytes in the new model. This means that the 289 states from before will actually take up more memory than the 480 states from the new model. The simpler model usually wins in a battle for complexity control.
 
 
