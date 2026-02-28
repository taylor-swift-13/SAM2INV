int main1(int m,int n){
  int c, b, p, l;

  c=m+12;
  b=0;
  p=n;
  l=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p + l == n + m;
  loop invariant b == p - n;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant p + l == \at(n, Pre) + \at(m, Pre);
  loop invariant p - l - 2*b == \at(n, Pre) - \at(m, Pre);
  loop invariant l + b == \at(m, Pre);
  loop invariant p >= \at(n, Pre);
  loop invariant 0 <= b;
  loop invariant c == m + 12;
  loop invariant l == m - b;
  loop invariant p == n + b;
  loop invariant b >= 0;
  loop invariant c == \at(m, Pre) + 12;
  loop invariant p == \at(n, Pre) + b;
  loop invariant l <= \at(m, Pre);
  loop invariant p + l == m + n;
  loop invariant p >= n;
  loop invariant l <= m;
  loop assigns p, l, b;
*/
while (1) {
      p = p+1;
      l = l-1;
      b = b+1;
  }

}
