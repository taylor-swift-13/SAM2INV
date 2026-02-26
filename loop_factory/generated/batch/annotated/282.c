int main1(int b,int n){
  int m, s, k, v;

  m=(b%7)+6;
  s=0;
  k=n;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(n, Pre) + 3*s;
  loop invariant v == -4 + 4*s;
  loop invariant m == (\at(b, Pre) % 7) + 6;
  loop invariant 0 <= s;
  loop invariant s <= m;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == (b % 7) + 6;
  loop invariant k == n + 3*s;
  loop assigns k, v, s;
*/
while (s<=m-1) {
      k = k+3;
      v = v+4;
      s = s+1;
  }

}
