int main1(int d){
  int ul, t1, n5, a, s2;
  ul=d-8;
  t1=0;
  n5=0;
  a=2;
  s2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 2 + n5*(n5 - 1)/2;
  loop invariant s2 == n5*(n5 + 1)/2;
  loop invariant 0 <= n5;
  loop invariant ul == \at(d, Pre) - 8;
  loop assigns a, n5, s2;
*/
while (n5<ul) {
      a = a + n5;
      n5++;
      s2 = s2 + n5;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t1;
  loop invariant ul == \at(d, Pre) - 8;
  loop invariant d == \at(d, Pre) + t1 * (a - t1) + ((t1 * (t1 + 1)) / 2);
  loop assigns a, d, t1;
*/
while (1) {
      a++;
      d = d + a;
      t1 = t1 + 1;
      if (t1>=ul) {
          break;
      }
  }
}