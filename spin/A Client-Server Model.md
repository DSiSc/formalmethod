

#  A Client-Server Model
It is relatively simple to create SPIN models with a dynamically changing number of active processes. Each newly created process can declare and instantiate its own set of local variables, so through the creation of a new process we can also create additional message channels. It may be somewhat confusing at first that message channel identifiers can have a process local scope, if declared within a proctype body, but that the message channels themselves are always global objects. The decision to define channels in this way makes it possible to restrict the access to a message channel to only specifically identified processes: message channels can be passed from one process to another. We will use this feature in the design of a simple, and fairly generic client-server model.

We will design a system with a single, fixed server that can receive requests from clients over a known global channel. When the server accepts a request for service, it assigns that request to an agent and provides a private channel name to the client that the client can use to communicate with the agent. The remainder of the transaction can now place between agent and client, communicating across a private channel without further requiring the intermediacy of the server process. Once the transaction is complete, the agent returns the identifier for the private channel to the server and exits.

Figure 15.5 shows the design of the agent and server processes. The fixed global channel on which the server process listens is declared as a rendezvous port called server. The server process has a private, locally declared, set of instantiated channels in reserve. We have given the server process a separate local channel, named pool, in which it can queue the channels that have not yet been assigned to an agent. The first few lines in the server process declaration fill up this queue with all available channels.

Figure 15.5 Agent and Server Processes

```
#define N         2
mtype = { request, deny, hold, grant, return };

chan server = [0] of { mtype, chan };

proctype Agent(chan listen, talk)
{
        do
        :: talk!hold(listen)
        :: talk!deny(listen) -> break
        :: talk!grant(listen) ->
wait:           listen?return; break
        od;
        server!return(listen)
}

active proctype Server()
{       chan agents[N] = [0] of { mtype };
        chan pool = [N] of { chan };
        chan client, agent;
        byte i;

        do
        :: i < N -> pool!agents[i]; i++
        :: else -> break
        od;

end:    do
        :: server?request(client) ->
                if
                :: empty(pool) ->
                        client!deny(0)
                :: nempty(pool) ->
                        pool?agent;
                run Agent(agent,client)
                fi
        :: server?return(agent) ->
                pool!agent
  od
}
```
A client sending a request to the server attaches the name of the channel where it will listen for responses from the server or the server's agent. If the channel pool is empty at this point, the server has no choice but to deny the request immediately. If a channel is available, an agent process is started and the name of the new private channel is passed to that agent, together with the channel through which the client can be reached. The server now goes back to its main loop, waiting for new client requests. Eventually, when the client transaction is complete, the server's agent will return the now freed up private channel, so that the server can add it back into its pool of free channels.

We have set up the agent to randomly decide to either grant or deny a request, or to inform the client that the request is on hold. (Think of a library system, where a user can request books. In some cases a book can be on loan, and the user may be informed that the book was placed on hold.) If the request is granted, the agent will move to a wait state where it expects the client to eventually send a return response, signifying that the transaction is now complete. The agent process will now notify the server that the private channel can be freed up again, and it terminates.

Figure 15.6 shows the structure of the client process for this system. The client has its own private channel that it reserves for communications with the server. It initiates the communication, after a timeout in this case, by sending a first request to the server on the known global channel, with its own channel identifier attached. It will now wait for the response from either the server or the server's agent. A denial from the server brings the client back to its initial state, where it can repeat the attempt to get a request granted. A hold message is simply ignored by this client, although in an extended model we could consider giving the client the option of canceling its request in this case. When the request is granted, the client will faithfully respond with a return message, to allow the server's agent to conclude the transaction.

Figure 15.6 The Client Processes
```
#define M        2

active [M] proctype Client()
{       chan me = [0] of { mtype, chan };
        chan agent;

end:    do
        :: timeout ->
               server!request(me);
               do
               :: me?hold(agent)
               :: me?deny(agent) ->
                       break
               :: me?grant(agent) ->
                       agent!return;
                       break
               od
        od
}
```
In this model, we have both dynamic process creation and the passing of channel identifiers from one process to the next. Dynamic process creation in a model such as this one can sometimes hold some surprises, so it will be worth our while to try some basic verification runs with this model. Clearly, the complexity of the model will depend on the number of client processes and the maximum number of agents that the server can employ. We will start simple, with just two client processes and maximally two agents. The verifi-cation then proceeds as follows:


```
$ spin -a client_server.pml
$ cc -o pan pan.c
$ ./pan
(Spin Version 4.0.7 -- 1 August 2003)
        + Partial Order Reduction

Full statespace search for:
        never claim             - (none specified)
        assertion violations    +
        acceptance cycles       - (not selected)
        invalid end states      +

State-vector 72 byte, depth reached 124, errors: 0
     190 states, stored
      74 states, matched
     264 transitions (= stored+matched)
       0 atomic steps
hash conflicts: 0 (resolved)
(max size 2^18 states)

1.573 memory usage (Mbyte)

unreached in proctype Agent
          (0 of 11 states)
unreached in proctype Server
        line 33, state 11, "client!deny,0"
        line 41, state 22, "-end-"
        (2 of 22 states)
unreached in proctype Client
        line 61, state 15, "-end-"
        (1 of 15 states)
```
Perhaps the one surprising detail in this result is that the statement on line 33, where the server summarily has to deny the request because its pool of available private channels is found to be empty, is not reachable. Given that the number of private channels in the server was defined to be equal to the number of clients, this result is easily understood. We can try to confirm our initial understanding of this phenomenon by increasing the number of client processes to three, without changing the number of channels declared in the server. Our expectation is now that the one unreachable statement in the server should disappear. This is the result:

```
$ spin -a client_server3.pml
$ cc -o pan pan.c
$ ./pan
(Spin Version 4.0.7 -- 1 August 2003)
        + Partial Order Reduction

Full statespace search for:
      never claim               - (none specified)
      assertion violations      +
      acceptance cycles         - (not selected)
      invalid end states        +

State-vector 84 byte, depth reached 331, errors: 0
     935 states, stored
     393 states, matched
    1328 transitions (= stored+matched)
       0 atomic steps
hash conflicts: 0 (resolved)
(max size 2^18 states)

1.573 memory usage (Mbyte)

unreached in proctype Agent
        (0 of 11 states)
unreached in proctype Server
        line 33, state 11, "client!deny,0"
        line 41, state 22, "-end-"
        (2 of 22 states)
unreached in proctype Client
        line 62, state 15, "-end-"
        (1 of 15 states)

```
We can see that the number of reachable states increased, as expected given that we have more processes running in this system. But the statement on line 33 is still unreachable. What is going on?

Now we look more closely at the way in which we have defined the client processes. Note that a client process can only initiate a new request when timeout is true. This only happens if no other process in the entire system can make a step. This means that effectively only one of the three client processes will be executing in this system at a time. (Exercise: try to find a way to prove by model checking that this is true.) The three clients have different process identifiers, so each of the clients generates a different set of system states when it executes. The symmetry in this system is not automatically exploited by SPIN.

As an experiment, we can replace the timeout condition with true, and see if this helps to exercise the rogue statement. This is most easily done by adding a macro definition to the model, for instance, as follows:

```

#define timeout true


Repeating the verification run now produces the following surprising result:



$ ./pan
error: max search depth too small
pan: out of memory
        2.68428e+008 bytes used
        102400 bytes more needed
        2.68435e+008 bytes limit
hint: to reduce memory, recompile with
 -DCOLLAPSE # good, fast compression, or
 -DMA=652 # better/slower compression, or
 -DHC # hash-compaction, approximation
 -DBITSTATE # supertrace, approximation
(Spin Version 4.0.7 -- 1 August 2003)
Warning: Search not completed
...

```
The search ran out of memory. What happened?

By making it possible for the client processes to initiate requests at any time, we made it possible for a client to resubmit a request for service before the agent process that handled its last request has terminated. Consider, for instance, a request that was granted. After the client concludes the transaction by sending its return message, the agent process still has a number of steps to take before it can terminate. It must, for instance, first return the identifier of the now freed up private channel back to the server. If the client is fast enough, it can initiate a new transaction before the agent has completed the handling of its last transaction. This means that the process identificatio number of the last agent process cannot be recycled and reassigned for the new tranaction: the number of running agent processes can increase arbitrarily far. Most of these agent processes will eventually reach their termination state, where they could die. Because process death can only happen in stack order, the newly created agent processes now prevent the older processes from dying.

Though annoying, this potentially infinite increase in resource consumption does reflect a real hazard scenario that could also happen in a real system execution, so it is not without value. Our job as system designers is to find a way to make sure that this scenario cannot happen, by modifying the system design.

The best way to prevent the potential for runaway resource consumption is at the source: in the client processes. Sadly, there is no general rule for how this is best done: it will depend on the specifics of the model that one is using. In this case, we can easily make sure that no new client request can be submitted until the agent process for prior requests have terminated by replacing the timeout with a slightly more restrictive condition than true. The condition we will use in this model is as follows:

```

#define timeout (_nr_pr <= N+M)

```
The variable _nr_pr is a predefined system variable (see the manual pages) that gives the precise number of active processes in the model. How many processes should we maximally have in this model? There are M client processes, one server process, and maximally N agent processes. This gives an upper limit of (N+M+1) active processes. When a client is about to submit a new request, though, it should have no active agent process associated with itself anymore, so the maximum number of active processes in the system at the time that a new request is made should not be larger than (N+M).

If we add this condition to the model and repeat the verification we see the following result:

```

$ ./pan -m30000
(Spin Version 4.0.7 -- 1 August 2003)
        + Partial Order Reduction
Full statespace search for:
        never claim             - (none specified)
        assertion violations    +
        acceptance cycles       - (not selected)
        invalid end states      +

State-vector 108 byte, depth reached 26939, errors: 0
  133932 states, stored
  306997 states, matched
  440929 transitions (= stored+matched)
       0 atomic steps
hash conflicts: 47515 (resolved)
(max size 2^18 states)

Stats on memory usage (in Megabytes):
15.536   equivalent memory usage for states
7.194    actual memory usage for states (compression: 46.30%)
         State-vector as stored = 46 byte + 8 byte overhead
1.049    memory used for hash table (-w18)
0.960    memory used for DFS stack (-m30000)
9.177    total actual memory usage

unreached in proctype Agent
        (0 of 11 states)
unreached in proctype Server
        line 41, state 22, "-end-"
        (1 of 22 states)
unreached in proctype Client
        line 63, state 15, "-end-"
         (1 of 15 states)
```

This is the result we were expecting when we tried to change timeout into true: all statements in the model, including the pesky statement on line 33, are now reachable, though at the expense of a considerable increase of the reachable state space.

As a general rule, when you see apparently infinite growth of the state space, signified by an apparently uncontrollable growth of either the state vector or the search depth, it is worth looking carefully at all the run statements in the model, to see if a scenario like the one we have discussed here is possible.
 

