int main1(){
  int f0z, q6, c9k, xep, ajhg;
  f0z=1-10;
  q6=0;
  c9k=2;
  xep=0;
  ajhg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ajhg == q6;
  loop invariant q6 >= 0;
  loop invariant c9k >= 2;
  loop invariant xep == q6 % 6;
  loop invariant c9k == 2 + q6 / 6;
  loop assigns ajhg, xep, c9k, q6;
*/
while (q6<=f0z-1) {
      ajhg += 1;
      xep = xep + 1;
      if (xep>=6) {
          xep -= 6;
          c9k += 1;
      }
      q6 += 1;
  }
}