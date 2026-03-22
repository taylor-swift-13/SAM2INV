int main1(){
  int c9, q1rg, x, b, kr, lc, l;
  c9=1*2;
  q1rg=0;
  x=1;
  b=0;
  kr=q1rg;
  lc=q1rg;
  l=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lc == 0;
  loop invariant c9 == 2;
  loop invariant l == 4;
  loop invariant x >= 1;
  loop invariant b == ( (x-1) * x * (2 * x - 1) ) / 6;
  loop invariant kr == ( ( (x - 1) * x * x * (x + 1) ) ) / 12 + 4 * (x - 1);
  loop invariant x <= c9 + 1;
  loop assigns b, x, kr;
*/
while (x<=c9) {
      b = b+x*x;
      x = x + 1;
      kr += b;
      kr = kr+lc+l;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lc <= l;
  loop invariant lc >= 0;
  loop invariant l == 4;
  loop invariant c9 == 2;
  loop invariant lc <= l - 1;
  loop assigns lc;
*/
while (1) {
      lc = lc + 1;
      if (lc>=l) {
          break;
      }
  }
}