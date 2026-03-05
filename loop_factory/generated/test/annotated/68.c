int main1(int j,int p){
  int hr, fx;
  hr=j;
  fx=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hr == \at(j, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= fx;
  loop invariant fx <= 6;
  loop invariant fx % 2 == 0;
  loop invariant j - fx >= hr;
  loop assigns fx, j;
*/
while (fx<hr) {
      fx = (fx+1)%6;
      fx = fx + 1;
      j += fx;
  }
}