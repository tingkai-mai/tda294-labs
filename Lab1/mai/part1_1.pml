#define N 4
int forkUserCount[N]; 

proctype phil(int id) {
  int firstForkIndex = id;
  int secondForkIndex = (id+1) % N;
  do
    :: printf("Philosopher %d is thinking\n", id);
      atomic {
        forkUserCount[firstForkIndex] == 0 && forkUserCount[secondForkIndex] == 0;
        forkUserCount[firstForkIndex]++;
        forkUserCount[secondForkIndex]++;
        forkUserCount[firstForkIndex] = true;
        forkUserCount[secondForkIndex] = true;
        printf("Philosopher %d is eating with forks %d and %d\n", id, firstForkIndex, secondForkIndex);
        forkUserCount[firstForkIndex]--;
        forkUserCount[secondForkIndex]--;
      }
 od
}

active proctype verifier() {
  int i = 0;
  for (i : 0 .. N-1) {
    assert(forkUserCount[i] <= 1);
  }
}

init  {
  int i = 0;
  int j = 0;

  for (j : 0 .. N-1)  {
    forkUserCount[j] = false;
  }

  do
  :: i >= N -> break
  :: else -> 
      run phil(i);
	    i++
  od
}