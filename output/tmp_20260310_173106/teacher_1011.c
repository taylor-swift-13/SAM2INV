int main1(int b,int n){
  int h, v, k;

  h=n;
  v=0;
  k=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(n, Pre);
  loop invariant v % 2 == 0;
  loop invariant v >= 0;
  loop invariant k == -4 + 6 * ((v + 4) / 6);
  loop invariant k + 4 == 6 * ((v + 5) / 6);
  loop invariant (k + 4) % 6 == 0;
  loop invariant k >= -4;
  loop invariant h < 0 || v <= h + 1;

  loop invariant h == n;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant 0 <= v;
  loop invariant k == -4 + 6 * ((v + 5) / 6) && v % 2 == 0 && v >= 0;

  loop invariant h == \at(n, Pre) && n == \at(n, Pre) && b == \at(b, Pre) && (k + 4) % 6 == 0;

  loop invariant (k - 2) % 6 == 0;
  loop assigns k, v;
*/
while (v<h) {
      if ((v%3)==0) {
          k = k+6;
      }
      v = v+2;
  }
/*@
  assert !(v<h) &&
         (h == \at(n, Pre));
*/


}
