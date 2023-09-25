NS2:
I used acceptance mode in SPIN to verify my answer, as we expect that eventually, statusA and statusB will be both ok.

Acceptance mode is used to check if  liveness property is held, where something "good" will eventually happen. In this question, we define that something "good" happens if (statusA == ok && statusB == ok). Thus, we want to check that this property eventually happens, thus using acceptance mode is appropriate.

NOTE: Why does running with -f create some error?

```
ltl task2: <> (((statusA==ok)) && ((statusB==ok)))
error: p.o. reduction not compatible with fairness (-f) in models
       with rendezvous operations: recompile with -DNOREDUCE
```

NS3:
