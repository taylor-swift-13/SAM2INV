int main1(int m,int p){
  int q, k, g, v;

  q=p+11;
  k=3;
  g=3;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == k*(k-1)/2;
  loop invariant v == 1;
  loop invariant q == p + 11;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant k >= 3;
  loop invariant v == 1 && q == p + 11;
  loop invariant g - k*(k-1)/2 == 0;
  loop invariant v > 0;
  loop invariant v >= 1;
  loop invariant g == k*(k-1)/2 && v == 1 && k >= 3;
  loop invariant q == \at(p, Pre) + 11 && p == \at(p, Pre) && m == \at(m, Pre);
  loop invariant g == k*(k - 1)/2 && q == p + 11 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant g >= 3;
  loop invariant p == \at(p,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant g == 3*k - 6 + ((k - 3) * (k - 4)) / 2;
  loop invariant q == \at(p, Pre) + 11;
  loop assigns g, v, k;
*/
while (1) {
      g = g+k;
      v = v*v;
      k = k+1;
  }

}
