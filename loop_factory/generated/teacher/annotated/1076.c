int main1(int a,int n){
  int v, r, b, m;

  v=n+3;
  r=3;
  b=r;
  m=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b + n == 3 + m;
  loop invariant v == n + 3;

  loop invariant r >= 3;
  loop invariant n == \at(n, Pre);
  loop invariant a == \at(a, Pre);

  loop invariant n == \at(n, Pre) && v == n + 3;
  loop invariant b - m == 3 - n && v == n + 3;

  loop invariant b - m == 3 - n;

  loop invariant b == m - n + 3;
  loop invariant v == \at(n, Pre) + 3;
  loop invariant n == \at(n, Pre) && a == \at(a, Pre) && v == \at(n, Pre) + 3;

  loop invariant m == b + \at(n, Pre) - 3;

  loop invariant b == 3 + m - n;

  loop invariant r >= 3 && (r <= v || v < 3) && n == \at(n, Pre) && a == \at(a, Pre);
  loop invariant b == m + 3 - \at(n, Pre);

  loop assigns b, m, r;
*/
while (r<v) {
      b = b+m;
      m = m+m;
      r = r+1;
  }

}
