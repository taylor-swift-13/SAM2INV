int main1(int b){
  int r, m, v, z;

  r=b-1;
  m=r;
  v=r;
  z=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(b, Pre) - 1;
  loop invariant z == r;
  loop invariant (1 + 2*r) != 0 ==> (v - r) % (1 + 2*r) == 0;
  loop invariant r == b - 1;
  loop invariant v <= r;
  loop invariant z == b - 1;
  loop invariant v >= r;
  loop invariant (v - r) % (1 + 2 * z) == 0;
  loop invariant (v - r) % (1 + 2*r) == 0;
  loop assigns v;
*/
while (v<r) {
      if (v<r) {
          v = v+1;
      }
      v = v+z+z;
  }

}
