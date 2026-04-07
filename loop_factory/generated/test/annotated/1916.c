int main1(){
  int d, rg, as, r7b, oz, o7v, cer, b;
  d=1;
  rg=0;
  as=8;
  r7b=15;
  oz=0;
  o7v=rg;
  cer=d;
  b=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oz == rg % 2;
  loop invariant cer == rg + 1;
  loop invariant as + r7b == 23;
  loop invariant 2 * b == (rg * (rg + 1));
  loop invariant 4 * rg <= o7v <= 5 * rg;
  loop invariant d == 1;
  loop invariant as == 8 + (rg % 2);
  loop invariant 0 <= rg <= d;
  loop assigns as, b, cer, o7v, oz, r7b, rg;
*/
while (rg<d) {
      if (oz==0) {
          as += 1;
          r7b--;
          oz = 1;
      }
      else {
          as = as - 1;
          r7b = r7b + 1;
          oz = 0;
      }
      rg++;
      if (rg+4<=b+d) {
          o7v = o7v + oz;
      }
      o7v += 4;
      b = b + rg;
      cer += 1;
  }
}