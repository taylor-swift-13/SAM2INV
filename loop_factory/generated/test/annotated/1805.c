int main1(){
  int l7h, krw, t6, qh;
  l7h=10;
  krw=1;
  t6=0;
  qh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qh == 3 * (10 - l7h);
  loop invariant t6 == 3 * ((10 - l7h) / 2);
  loop invariant 0 <= l7h;
  loop invariant l7h <= 10;
  loop invariant 1 <= krw;
  loop assigns l7h, krw, t6, qh;
*/
while (1) {
      if (!(l7h > 0)) {
          break;
      }
      l7h--;
      krw = krw * 2;
      t6 = t6+(qh%6);
      qh = qh + 3;
  }
}