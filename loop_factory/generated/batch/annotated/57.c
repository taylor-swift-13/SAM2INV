int main1(int n,int p){
  int u, d, j, z, v, q;

  u=(p%37)+18;
  d=0;
  j=d;
  z=p;
  v=2;
  q=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant j == 4*d && v == 2 + 2*d && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant j == 4 * d;
  loop invariant v == 2 * d + 2;
  loop invariant d >= 0 && (u <= 0 || d <= u);
  loop invariant p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant d >= 0;
  loop invariant v == 2 + 2*d;

  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && u == (\at(p, Pre) % 37) + 18;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == (\at(p, Pre) % 37) + 18;
  loop assigns d, j, v;
*/
while (d<u) {
      j = j+4;
      v = v+2;
      d = d+1;
  }

}
