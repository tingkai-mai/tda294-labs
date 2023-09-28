#define N 4

/*
Creates a channel array for the number of forks available
*/

chan forks[N] = [1] of {byte};
byte forks_counter[N];
byte eaten[N];

proctype phil(int id) {
  /*
  Initialize fork 1 and fork 2
  */
  
  byte f1 = N + 1; // N + 1 represents that the fork is empty.
  byte f2 = N + 1;
  do
    :: printf("Philosopher %d is thinking\n", id);
        if 
          /*
          If id is odd, take the left fork first
          then take the right fork
          */
          :: (id % 2 == 1) ->
            if 
              :: (f1 == N + 1) -> forks[id] ? f1;
              forks_counter[id]++;
            fi
            assert(forks_counter[id] <= 1);
          
            if 
              :: (f2 == N + 1) -> forks[(id + 1) % N] ? f2;
              forks_counter[(id + 1) % N]++;
            fi
            assert(forks_counter[(id + 1) % N] <= 1);
          
          /*
          If id is even, take the right fork first
          then take the left fork
          */
          :: (id % 2 == 0) ->
            if 
              :: (f2 == N + 1) -> forks[(id + 1) % N] ? f2;
              forks_counter[(id + 1) % N]++;
            fi
            assert(forks_counter[(id + 1) % N] <= 1);
          
            if 
              :: (f1 == N + 1) -> forks[id] ? f1;
              forks_counter[id]++;
            fi
            assert(forks_counter[id] <= 1);
        fi
        
       printf("Philosopher %d is eating with forks %d and %d\n", id, f1, f2);
       eaten[id] = 1;
       /*
       Reset the variables
       */
       f1 = N + 1;
       f2 = N + 1;
       forks_counter[id]--;
       forks_counter[(id + 1) % N]--;
       forks[id] ! id;
       forks[(id + 1) % N] ! (id + 1) % N;
  od
}

init  {
  /*
  Initialize forks
  */
  int j = 0;
  do
    :: j >= N -> break
    :: else -> forks[j] ! j; j++;
  od
    
  int i = 0;

  do
  :: i >= N -> break
  :: else -> run phil(i);
         i++
  od
}

ltl allPhilosophersEaten { <> (eaten[0] == 1 && eaten[1] == 1 && 
    eaten[2] == 1 && eaten[3] == 1) }

ltl noForkHasMoreThanOneOwner { [] (forks_counter[0] <= 1 && forks_counter[1] <= 1 && forks_counter[2] <= 1 && forks_counter[3] <= 1)}