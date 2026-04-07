int main1(int j){
  int x, x2, z5;
  x=j;
  x2=1;
  z5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j, Pre) + z5*(z5+1)/2;
  loop invariant z5 >= 0;
  loop invariant x2 >= 1;
  loop invariant x == \at(j, Pre);
  loop assigns j, x2, z5;
*/
while (x2<x) {
      z5++;
      x2 = 2*x2;
      j = j + z5;
  }
}