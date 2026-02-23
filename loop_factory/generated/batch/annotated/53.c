int main1(int k,int p){
  int g, l, m, v, d;

  g=54;
  l=g;
  m=k;
  v=2;
  d=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(k, Pre) + l - 54;
  loop invariant (0 <= l) && (l <= 54);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant g == 54;
  loop invariant m - l == k - 54;
  loop invariant 0 <= l && l <= 54;
  loop invariant m - l == \at(k, Pre) - 54;
  loop invariant v == 2;
  loop invariant d == -4;
  loop invariant 0 <= l;
  loop invariant l <= 54;
  loop invariant l >= 0;
  loop invariant m <= k;
  loop invariant m >= k - 54;
  loop assigns m, l;
*/
while (l>0) {
      m = m+v+d;
      m = m+1;
      l = l-1;
  }

}
