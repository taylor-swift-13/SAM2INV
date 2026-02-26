int main1(int b,int n){
  int m, s, k, v;

  m=(b%7)+6;
  s=0;
  k=n;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant v <= 0;
  loop invariant m == (b % 7) + 6;
  loop invariant 0 <= s;
  loop invariant m == (\at(b, Pre) % 7) + 6;
  loop invariant s >= 0;
  loop invariant s <= m;
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant v <= 0 && -4 <= v && ((n >= 0) ==> (k >= n)) && ((n < 0) ==> (k <= n));

  loop invariant v >= -4;
  loop assigns k, v, s;
*/
while (s<=m-1) {
      k = k*2;
      v = v/2;
      s = s+1;
  }

}
