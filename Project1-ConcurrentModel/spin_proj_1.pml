/**
Devon Gosnick
Chanpech Hoeng
CS 4711 R01 
SPIN Project 1
*/

#define N 10

int A[N];
bool locked[N];

init {
   atomic {
      byte i;
      for(i : 0 .. N-1) {
         A[i] = i + 1;
         locked[i] = false;
      }
   }
}

inline getRandIndex() { 
   do
      :: (targetIndex < 255) -> targetIndex++
      :: (targetIndex % N != sourceIndex) -> break
   od
   targetIndex = targetIndex % N;
}

inline swap(i, j) {
   int temp = A[i]
   A[i] = A[j]
   A[j] = temp
}

active[N] proctype proc() {
   byte sourceIndex = _pid - 1; // Source process's array index
   byte targetIndex = 0; // Target process's array index
   getRandIndex();
   
   printf("process %d entering trying section\n", _pid);
   TS: atomic{!locked[targetIndex] -> locked[targetIndex] = true;}

   printf("process %d entering critical section (target: process %d)\n", _pid, targetIndex + 1);
   CS: swap(sourceIndex, targetIndex);
   locked[targetIndex] = false;
}
