int main1(int a){
  int g, vw, g3, pbhy, u, d;
  g=a*3;
  vw=g+3;
  g3=3;
  pbhy=-4;
  u=a;
  d=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == a*3;
  loop invariant vw == g + 3;
  loop invariant g3 == 3 + a*(pbhy + 4);
  loop invariant u  == a + (pbhy + 4) * vw;
  loop invariant pbhy >= -4;
  loop assigns g3, pbhy, u;
*/
while (pbhy<=g-1) {
      g3 = g3 + a;
      u = u + vw;
      pbhy = pbhy + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == a*3;
  loop invariant d == a * (vw - (g + 3) + 1);
  loop assigns vw, d, pbhy;
*/
while (vw<g) {
      vw = vw + 1;
      d = d + a;
      pbhy = pbhy+(vw%6);
  }
}