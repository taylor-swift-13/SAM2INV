int main1(int g){
  int qxl, n, xn, d5u1;
  qxl=118;
  n=0;
  xn=0;
  d5u1=qxl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d5u1 == qxl + 3*n;
  loop invariant xn == 2*n;
  loop invariant g == \at(g, Pre) + n*qxl + 3 * ((n*(n+1))/2);
  loop invariant d5u1 == 118 + 3*n;
  loop invariant 0 <= n <= qxl;
  loop assigns d5u1, n, xn, g;
*/
while (n < qxl) {
      d5u1 = d5u1 + 3;
      n += 1;
      xn += 2;
      g = g + d5u1;
  }
}