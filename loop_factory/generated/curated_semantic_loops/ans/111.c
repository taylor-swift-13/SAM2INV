int main1(int m,int n){
  int v, k, h, s;

  v=42;
  k=v;
  h=m;
  s=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= 0;
  loop invariant k <= 42;
  loop invariant k % 3 == 0;

  loop invariant m == \at(m, Pre);
  loop invariant h*3 - 3*m == (2*m + 1) * (42 - k);
  loop invariant h == m + (2*m + 1) * ((42 - k) / 3) &&
                   k % 3 == 0 &&
                   0 <= k && k <= 42 &&
                   s == m;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant 3*(h - \at(m, Pre)) == (42 - k)*(2*s + 1);
  loop invariant 0 <= k && k <= 42;
  loop invariant s == \at(m, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant s == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (42 - k) % 3 == 0;
  loop invariant h == \at(m, Pre) + ((42 - k)/3) * (2*s + 1);
  loop invariant s == m && 3*(h - m) == (42 - k) * (2*s + 1);
  loop invariant v == 42;
  loop invariant h == m + (2*m + 1) * ((42 - k) / 3);
  loop invariant s == m;
  loop invariant s == \at(m, Pre) && 0 <= k && k <= v && (v - k) % 3 == 0;
  loop invariant h == s + ((v - k)/3) * (2*s + 1);
  loop assigns h, k;
*/
while (k>=3) {
      h = h+s+s;
      h = h+1;
      k = k-3;
  }
/*@
  assert !(k>=3) &&
         (k >= 0);
*/


}
