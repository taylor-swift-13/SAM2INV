int main1(int b,int n){
  int m, s, k, v;

  m=(b%7)+6;
  s=0;
  k=n;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= 0;
  loop invariant s <= m;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant m == b % 7 + 6;
  loop invariant m == (b%7) + 6;
  loop invariant 0 <= s;
  loop invariant (n >= 0) ==> (k >= n);
  loop invariant m == (\at(b, Pre) % 7) + 6;
  loop assigns k, s;
*/
while (s<=m-1) {
      k = k*2;
      s = s+1;
  }

}
