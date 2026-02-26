int main1(int k,int p){
  int z, d, v;

  z=37;
  d=0;
  v=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 37;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= 0;
  loop invariant v % 24 == 0;
  loop invariant v % 6 == 0;
  loop assigns v;
*/
while (1) {
      v = v+4;
      v = v*6;
  }

}
