int main1(int a,int n){
  int w, u, v, q;

  w=n;
  u=w;
  v=u;
  q=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= w;
  loop invariant 2*(a - q) == v - w;
  loop invariant a == \at(a,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant w == \at(n, Pre);
  loop invariant v + 2*q == \at(n, Pre) + 2 * \at(a, Pre);
  loop invariant v >= \at(n, Pre);
  loop invariant q <= \at(a, Pre);
  loop invariant w == n;
  loop invariant v <= w + 1;
  loop invariant q <= a;
  loop invariant v >= n - 1;
  loop invariant (v - n) % 2 == 0;
  loop invariant q == a - ((v - n) / 2);
  loop assigns v, q;
*/
while (v<w) {
      if (v<w) {
          v = v+1;
      }
      v = v+1;
      q = q-1;
  }

}
