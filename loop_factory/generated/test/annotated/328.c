int main1(){
  int hd, qh, m, x, yr0, ai;
  hd=1;
  qh=hd;
  m=0;
  x=-4;
  yr0=1;
  ai=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qh == 1;
  loop invariant m >= 0;
  loop invariant x == m - 4;
  loop invariant yr0 >= 1;
  loop invariant m <= 5;
  loop invariant qh == hd;
  loop assigns m, x, yr0;
*/
while (1) {
      if (!(x<hd)) {
          break;
      }
      m++;
      x = x + 1;
      yr0 = yr0 + qh;
      yr0 = yr0*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hd == 1;
  loop invariant m >= 0;
  loop invariant yr0 >= 0;
  loop invariant ai >= 0;
  loop assigns ai, yr0, m;
*/
while (hd-m>0) {
      ai = ai + yr0;
      yr0 += hd;
      m = 0;
  }
}