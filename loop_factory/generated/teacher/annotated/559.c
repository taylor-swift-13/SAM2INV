int main1(int b,int k){
  int m, j, v, q;

  m=77;
  j=1;
  v=m;
  q=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 77;
  loop invariant j == 1;
  loop invariant v <= m + 1;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == 77;
  loop invariant q == k;
  loop invariant v >= 0;
  loop invariant (v - m) % 2 == 0;
  loop invariant v % 2 == 1;
  loop invariant v >= m;
  loop invariant v >= 77;
  loop assigns v, q;
*/
while (v<m) {
      if (v<m) {
          v = v+1;
      }
      v = v+j;
      q = q*q;
      q = q+v*q;
  }

}
