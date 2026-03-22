int main1(){
  int r, bm, n, s, j0b2, en, hi, lr, qh;
  r=1;
  bm=0;
  n=(1%20)+10;
  s=(1%15)+8;
  j0b2=r;
  en=r;
  hi=bm;
  lr=2;
  qh=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (n + s) + bm == 20;
  loop invariant j0b2 == 1 + 2*bm;
  loop invariant lr == 2 + 3*bm;
  loop invariant 0 <= bm <= 20;
  loop invariant 0 <= n <= 11;
  loop invariant 0 <= s <= 9;
  loop invariant qh >= 5;
  loop invariant r == 1;
  loop assigns n, s, bm, qh, en, j0b2, lr, hi;
*/
while (1) {
      if (!(n>0&&s>0)) {
          break;
      }
      if (bm%2==0) {
          n = n - 1;
      }
      else {
          s -= 1;
      }
      bm = bm + 1;
      if ((bm%6)==0) {
          qh = qh + bm;
      }
      en = en + 3;
      j0b2 += 2;
      lr = lr + 3;
      hi = hi+(bm%2);
      en += j0b2;
      hi = hi + en;
      en = qh-en;
  }
}