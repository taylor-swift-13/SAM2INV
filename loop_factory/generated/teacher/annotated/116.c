int main1(int b){
  int n, m, v, j;

  n=8;
  m=0;
  v=b;
  j=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 3*(v - \at(b, Pre));
  loop invariant v >= \at(b, Pre);
  loop invariant m % 3 == 0;
  loop invariant v == \at(b, Pre) + m / 3;
  loop invariant 0 <= m;
  loop invariant m <= n + 2;
  loop invariant b == \at(b, Pre);
  loop invariant v == b + m/3;
  loop invariant n == 8;

  loop assigns m, v;
*/
while (m<n) {
      v = v+1;
      m = m+3;
  }

}
