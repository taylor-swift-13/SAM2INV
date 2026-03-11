int main1(int n,int p){
  int u, d, j, z, v, q;

  u=(p%37)+18;
  d=0;
  j=d;
  z=p;
  v=2;
  q=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (d<u) {
      j = j+4;
      v = v+2;
      d = d+1;
  }
/*@
  assert !(d<u) &&
         (j == 4*d && v == 2 + 2*d && n == \at(n, Pre) && p == \at(p, Pre));
*/

}
