int main1(){
  int gjt, n, v4, ad, v0h;
  gjt=(1%28)+14;
  n=2;
  v4=0;
  ad=gjt;
  v0h=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v4 == ((n-1)*n*(2*n - 1))/6 - 1;
  loop invariant v0h == n*(n+1)/2 - 9;
  loop invariant ad == 3*n + 9;
  loop invariant 2 <= n <= gjt + 1;
  loop invariant 2 <= n && n <= gjt + 1;
  loop invariant v4 == (((n - 1) * n * (2 * n - 1)) / 6) - 1;
  loop invariant ad == (gjt + 3 * (n - 2));
  loop invariant 2 * v0h == (n * n + n - 18);
  loop invariant n >= 2;
  loop invariant n <= gjt + 1;
  loop invariant 6*(v4 + 1) == (n - 1) * n * (2 * n - 1);
  loop invariant 2 * v0h == n * (n + 1) - 18;
  loop invariant ad == gjt + 3 * (n - 2);
  loop invariant (v0h == (n * (n + 1)) / 2 - 9);
  loop assigns v4, n, ad, v0h;
*/
while (1) {
      if (!(n<=gjt)) {
          break;
      }
      v4 = v4+n*n;
      n += 1;
      ad = ad + 3;
      v0h += n;
  }
}