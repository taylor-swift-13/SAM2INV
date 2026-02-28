int main1(int b,int m,int n,int q){
  int g, i, s, z, d, v;

  g=41;
  i=g;
  s=n;
  z=m;
  d=6;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(n, Pre) + (41 - i) * (i + 42) / 2;
  loop invariant i >= 0;
  loop invariant s >= \at(n, Pre);
  loop invariant i <= 41;
  loop invariant s == n + (41 - i) * (42 + i) / 2;
  loop invariant 0 <= i <= 41;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant s == n + 861 - i*(i+1)/2;
  loop invariant 0 <= i;
  loop invariant s >= n;
  loop invariant s == \at(n, Pre) + (41 - i) * 41 - ((41 - i) * (41 - i - 1)) / 2;
  loop assigns s, i;
*/
while (i>=1) {
      s = s+i;
      i = i-1;
  }

}
