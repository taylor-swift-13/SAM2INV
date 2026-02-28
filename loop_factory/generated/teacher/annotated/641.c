int main1(int m,int q){
  int s, z, d, n, v, x;

  s=44;
  z=1;
  d=2;
  n=z;
  v=-1;
  x=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d - z == 1;
  loop invariant n == d * z - 1;
  loop invariant z >= 1;
  loop invariant d >= 2;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d == z + 1;
  loop invariant n == z*z + z - 1;
  loop invariant s == 44;
  loop invariant z == d - 1;
  loop invariant n == d*d - d - 1;
  loop invariant n >= 1;
  loop assigns d, n, z;
*/
while (1) {
      d = d+1;
      n = n+d;
      n = n+z;
      z = z+1;
  }

}
