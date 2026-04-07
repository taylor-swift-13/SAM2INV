int main1(int d){
  int ax6n, f7zu, r, cqc8, cv;
  ax6n=(d%23)+10;
  f7zu=0;
  r=0;
  cqc8=0;
  cv=ax6n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f7zu >= 0;
  loop invariant (ax6n >= 0 ==> f7zu <= ax6n);
  loop invariant r == f7zu * d;
  loop invariant cqc8 == (d * f7zu * (f7zu + 1)) / 2;
  loop invariant ax6n - 2 * f7zu <= cv;
  loop invariant cv <= ax6n + 2 * f7zu;
  loop invariant r == f7zu * \at(d, Pre);
  loop invariant 0 <= f7zu && (ax6n <= 0 || f7zu <= ax6n);
  loop invariant ax6n == (d % 23) + 10;
  loop invariant (f7zu < ax6n) ==> (ax6n - f7zu > 0);
  loop assigns r, f7zu, cqc8, cv;
*/
while (1) {
      if (!(f7zu < ax6n)) {
          break;
      }
      r += d;
      f7zu = f7zu + 1;
      cqc8 += r;
      cv = cv+(cqc8%3);
  }
}