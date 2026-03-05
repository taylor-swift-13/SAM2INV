int main1(int x){
  int nh8, bedu, ci;
  nh8=31;
  bedu=nh8;
  ci=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= \at(x, Pre);
  loop invariant nh8 == bedu && (ci == 0 || ci == nh8 + 1);
  loop invariant nh8 == 31;
  loop assigns ci, x;
*/
while (bedu-3>=0) {
      ci = nh8-ci;
      ci = ci + 1;
      x += ci;
  }
}