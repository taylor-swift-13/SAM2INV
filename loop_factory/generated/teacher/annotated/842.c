int main1(int k,int n,int p){
  int l, y, v, q, o, g;

  l=(n%7)+20;
  y=0;
  v=n;
  q=8;
  o=y;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 0;
  loop invariant v >= \at(n, Pre);
  loop invariant l == (\at(n, Pre) % 7) + 20;
  loop invariant (q == 8) || (q == o);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l == (n % 7) + 20;
  loop invariant v >= n;
  loop invariant q == o || q == 8;
  loop invariant q == 8 || q == 0;

  loop invariant (v == n && q == 8) || (v > n && q == 0);
  loop assigns v, q;
*/
while (1) {
      if (v>=l) {
          break;
      }
      if (o<=q) {
          q = o;
      }
      v = v+1;
  }

}
