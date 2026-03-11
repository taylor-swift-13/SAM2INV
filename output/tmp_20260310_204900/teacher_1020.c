int main1(int b,int p){
  int n, v, q, e;

  n=80;
  v=n+4;
  q=2;
  e=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 2;
  loop invariant q % 2 == 0;
  loop invariant 0 <= e && e <= n;
  loop invariant (q + 2) * e <= 4 * n;
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant (b == \at(b, Pre)) && (p == \at(p, Pre));

  loop invariant 2 <= q && q <= 2 * n;
  loop invariant e >= 0;

  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant q <= 2 * n;
  loop invariant q % 2 == 0 && q >= 2 && e >= 0 && e <= n && b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant p == \at(p, Pre) && b == \at(b, Pre) && 2 <= q && q <= 2 * n;
  loop assigns q, e;
*/
while (q<n) {
      if (q<n) {
          q = q+1;
      }
      q = q*2;
      e = e/2;
  }
/*@
  assert !(q<n) &&
         (q >= 2);
*/


}
