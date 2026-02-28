int main1(int b,int n){
  int m, s, k, v;

  m=(b%7)+6;
  s=0;
  k=m;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == m;
  loop invariant m == (b % 7) + 6;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m == (\at(b,Pre) % 7) + 6;
  loop invariant 0 <= m;
  loop invariant m <= 12;

  loop invariant k <= m;
  loop assigns k;
*/
while (1) {
      if (k+1<=m) {
          k = k+1;
      }
      else {
          k = m;
      }
  }

}
