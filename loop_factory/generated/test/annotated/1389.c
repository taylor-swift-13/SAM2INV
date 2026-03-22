int main1(){
  int gz, bw, yl, nu, g, d, s2;
  gz=1-7;
  bw=gz+7;
  yl=0;
  nu=1;
  g=6;
  d=0;
  s2=gz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yl == d*d*d;
  loop invariant nu == 3*d*d + 3*d + 1;
  loop invariant bw == gz + 7;
  loop invariant g == 6 + 6 * d;
  loop invariant d >= 0;
  loop invariant s2 == gz + bw*d;
  loop invariant s2 - d == gz;
  loop assigns d, yl, nu, s2, g;
*/
while (d<=gz) {
      d++;
      yl = yl + nu;
      nu = nu + g;
      s2 = s2 + bw;
      g += 6;
  }
}