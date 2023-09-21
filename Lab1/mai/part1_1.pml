#define N 4
bool isForkUsed[N]; 

int critical = 0;

proctype phil(int id) {
  printf("running\n");
  int firstForkIndex = id;
  int secondForkIndex = (id+1) % N;
  do
    :: printf("Philosopher %d is thinking\n", id);
      atomic {
        !isForkUsed[firstForkIndex] && !isForkUsed[secondForkIndex];
        critical++; 
        isForkUsed[firstForkIndex] = true;
        isForkUsed[secondForkIndex] = true;
        printf("Philosopher %d is eating with forks %d and %d\n", id, firstForkIndex, secondForkIndex);
        isForkUsed[firstForkIndex] = false;
        isForkUsed[secondForkIndex] = false;
        critical--;
      }
 od
}

active proctype verifier() {
  assert(critical <= 1);
}

init  {
  int i = 0;
  int j = 0;

  for (j : 0 .. N-1)  {
    isForkUsed[j] = false;
  }

  do
  :: i >= N -> break
  :: else -> 
      run phil(i);
	    i++
  od
  printf("End\n");
}