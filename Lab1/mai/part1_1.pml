#define N 4
#define EMPTY_USER 100
int forkUserCount[N]; 
int forkCurrentUser[N]; 
int hasEaten[N];

proctype phil(int id) {
  int firstForkIndex = id;
  int secondForkIndex = (id+1) % N;
  do
    :: printf("Philosopher %d is thinking\n", id);
      do
        :: id % 2 != 0 ->
          atomic {
            forkUserCount[firstForkIndex] == 0 && forkCurrentUser[firstForkIndex] == EMPTY_USER;
            forkCurrentUser[firstForkIndex] = id;
            forkUserCount[firstForkIndex] = forkUserCount[firstForkIndex] + 1;
            printf("Philosopher %d picked up fork %d\n", id, firstForkIndex);
          }
          atomic {
            forkUserCount[secondForkIndex] == 0 && forkCurrentUser[secondForkIndex] == EMPTY_USER;
            forkCurrentUser[secondForkIndex] = id;
            forkUserCount[secondForkIndex] = forkUserCount[secondForkIndex] + 1;
            printf("Philosopher %d picked up fork %d\n", id, secondForkIndex);
          }
          break;
        :: else ->
          atomic {
            forkUserCount[secondForkIndex] == 0 && forkCurrentUser[secondForkIndex] == EMPTY_USER;
            forkCurrentUser[secondForkIndex] = id;
            forkUserCount[secondForkIndex] = forkUserCount[secondForkIndex] + 1;
            printf("Philosopher %d picked up fork %d\n", id, secondForkIndex);
          }
          atomic {
            forkUserCount[firstForkIndex] == 0 && forkCurrentUser[firstForkIndex] == EMPTY_USER;
            forkCurrentUser[firstForkIndex] = id;
            forkUserCount[firstForkIndex] = forkUserCount[firstForkIndex] + 1;
            printf("Philosopher %d picked up fork %d\n", id, firstForkIndex);
          }
          break;
      od

      atomic {
        forkUserCount[firstForkIndex] == 1 && forkUserCount[secondForkIndex] == 1 && forkCurrentUser[firstForkIndex] == id && forkCurrentUser[secondForkIndex] == id;
        hasEaten[id] = 1;
        printf("Philosopher %d is eating with forks %d and %d\n", id, firstForkIndex, secondForkIndex);
        forkUserCount[firstForkIndex] = forkUserCount[firstForkIndex] - 1;
        forkUserCount[secondForkIndex] = forkUserCount[secondForkIndex] - 1;
        forkCurrentUser[firstForkIndex] = EMPTY_USER;
        forkCurrentUser[secondForkIndex] = EMPTY_USER;
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
    forkCurrentUser[j] = EMPTY_USER;
    hasEaten[j] = 0;
  }

  do
  :: i >= N -> break
  :: else -> 
      run phil(i);
	    i++
  od
}


ltl forksAreNotShared{ [] (
  forkUserCount[0] <= 1 && 
  forkUserCount[1] <= 1 && 
  forkUserCount[2] <= 1 && 
  forkUserCount[3] <= 1 
)};

ltl philHasEatenAtLeastOnce { []<> (
  hasEaten[0] == 1 ||
  hasEaten[1] == 1 || 
  hasEaten[2] == 1 || 
  hasEaten[3] == 1 
)}