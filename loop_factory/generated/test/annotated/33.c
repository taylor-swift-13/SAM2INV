int main1(int n){
  int p, hc, v5z9, t31;
  p=n;
  hc=2;
  v5z9=0;
  t31=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v5z9 == 4*(hc - 2);
  loop invariant t31 == p - v5z9;
  loop invariant p == \at(n, Pre);
  loop invariant v5z9 >= 0;
  loop invariant (hc == 2 ==> n == \at(n,Pre)) && (hc >= 3 ==> n == v5z9 - 8);
  loop assigns v5z9, t31, n, hc;
*/
while (1) {
      v5z9 += 4;
      t31 -= 4;
      n += v5z9;
      n = v5z9-8;
      hc += 1;
      if (hc>=p) {
          break;
      }
  }
}