#define N 4

/*
Creates a channel array for the number of forks available
*/

chan forks[N] = [1] of {byte};
byte forks_counter[N];

proctype phil(int id) {
  /*
  Initialize fork 1 and fork 2
  */
  
  byte f1 = N + 1;
  byte f2 = N + 1;
  do
    :: printf("Philosopher %d is thinking\n", id);
       do
       /*
       If both forks not taken: pick either forks
       If one fork is taken: take the other fork
       If both forks taken: break out of the loop
       */
         :: atomic {
            (f1 == N + 1) -> forks[id] ? f1;
            forks_counter[id]++;
            assert(forks_counter[id] <= 1)
         }
         :: atomic {
            (f2 == N + 1) -> forks[(id + 1) % N] ? f2;
            forks_counter[(id + 1) % N]++;
            assert(forks_counter[(id + 1) % N] <= 1)
         }
         :: else -> break
       od
       printf("Philosopher %d is eating with forks %d and %d\n", id, f1, f2);
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
    :: else -> forks[j] ! j; j++
  od
    
  int i = 0;

  do
  :: i >= N -> break
  :: else -> run phil(i);
         i++
  od
}