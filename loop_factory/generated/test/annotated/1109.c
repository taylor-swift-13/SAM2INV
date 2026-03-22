int main1(){
  int l3tt, gvgk, a, fx, r, g981, xz, p5;
  l3tt=1+20;
  gvgk=l3tt;
  a=1;
  fx=0;
  r=2;
  g981=13;
  xz=l3tt;
  p5=gvgk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gvgk == l3tt;
  loop invariant 1 <= a <= l3tt + 1;
  loop invariant fx == ((a - 1) * a * (2 * a - 1)) / 6;
  loop invariant r == a + 1;
  loop invariant xz == l3tt + (a - 1);
  loop invariant p5 == a * gvgk;
  loop invariant a >= 1;
  loop invariant a <= l3tt + 1;
  loop invariant xz == l3tt + a - 1;
  loop invariant p5 == gvgk * a;
  loop invariant fx == (a - 1) * a * (2 * a - 1) / 6;
  loop invariant a <= l3tt + 1 && xz == l3tt + (a - 1);
  loop invariant r == 2 + (a - 1) * (l3tt - gvgk + 1) && fx == (a - 1) * a * (2 * a - 1) / 6;
  loop invariant (r - a == 1) && (a <= l3tt + 1);
  loop assigns fx, a, r, xz, p5;
*/
while (a<=l3tt) {
      fx = fx+a*a;
      a++;
      r = r+l3tt-gvgk;
      r = r + 1;
      xz += 1;
      p5 = p5 + gvgk;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p5 >= 0;
  loop invariant xz >= 0;
  loop invariant g981 == g981;
  loop invariant r > g981;
  loop invariant (p5 >= 0);
  loop assigns p5, r, xz;
*/
while (1) {
      if (!(r<=g981)) {
          break;
      }
      p5 = p5+r*r;
      r = r + 1;
      xz = xz + g981;
      xz = xz + 7;
  }
}