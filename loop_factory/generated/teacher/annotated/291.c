int main1(int k,int p){
  int z, d, v;

  z=37;
  d=0;
  v=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= 0;
  loop invariant v % 2 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z == 37;
  loop invariant d == 0;
  loop invariant d <= z;
  loop invariant v <= d;
  loop assigns v;
*/
while (d<z) {
      v = v+4;
      v = v-6;
  }

}
