int main1(int y){
  int r, jgq, ixi;
  r=y;
  jgq=0;
  ixi=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ixi == 20 + 4*(jgq/8);
  loop invariant r == \at(y,Pre);
  loop invariant jgq % 8 == 0;
  loop invariant jgq >= 0;
  loop assigns ixi, jgq;
*/
for (; jgq<r; jgq += 8) {
      ixi += 4;
  }
}