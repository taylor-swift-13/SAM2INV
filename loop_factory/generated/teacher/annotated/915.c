int main1(int n,int p){
  int b, l, v, q;

  b=18;
  l=0;
  v=b;
  q=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + q == 18 + n;
  loop invariant l == 0 && q <= n && v >= 18 && (n - q) % 3 == 0 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant l == 0;
  loop invariant v >= 18;
  loop invariant q <= n;
  loop invariant b == 18;
  loop invariant (n - q) * (3 + l) == 3 * (v - b);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v + q == n + b;
  loop invariant v + q == n + b && l == 0;
  loop invariant q <= n && (v - b) % 3 == 0 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant v + q == b + n;
  loop invariant l == 0 && q <= n && (n - q) % 3 == 0;
  loop invariant 3*(v - 18) == (3 + l)*(n - q);
  loop invariant q <= n && (n - q) % 3 == 0 && v >= 18 && (v - 18) % (3 + l) == 0 && n == \at(n, Pre) && p == \at(p, Pre);

  loop invariant l == 0 && v + q == n + 18;
  loop invariant v >= 18 && q <= n && b == 18;
  loop assigns v, q;
*/
while (1) {
      v = v+3;
      q = q-3;
      v = v+l;
  }

}
