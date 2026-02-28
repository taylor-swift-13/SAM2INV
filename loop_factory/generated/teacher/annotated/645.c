int main1(int b,int n){
  int e, s, v, g, k;

  e=n;
  s=0;
  v=n;
  g=-5;
  k=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= \at(n,Pre);
  loop invariant k == \at(n,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant e == n;
  loop invariant g == -5 || g == \at(n,Pre);
  loop invariant k == n;
  loop invariant g == -5 || g == k;
  loop invariant e == \at(n, Pre);

  loop invariant (b == \at(b, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant (e == \at(n, Pre));
  loop invariant (v >= \at(n, Pre));
  loop invariant n == \at(n, Pre);
  loop invariant v >= n;
  loop invariant (g == -5) || (g == k);
  loop invariant v >= k;
  loop invariant e == k;
  loop assigns g, v;
*/
while (1) {
      if (k<=g) {
          g = k;
      }
      v = v+1;
  }

}
