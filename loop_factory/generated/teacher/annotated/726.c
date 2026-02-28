int main1(int b,int k,int n,int q){
  int i, j, v, p;

  i=b+12;
  j=i;
  v=3;
  p=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 3 + 6*(j - i);
  loop invariant p == n + 3*(j - i)*(j - i) + 6*(j - i);
  loop invariant j >= i;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == b + 12;
  loop invariant j <= i;
  loop invariant v >= 3;
  loop invariant p >= n;
  loop invariant v % 3 == 0;
  loop invariant p == n + 3*(j - i)*(j - i + 2);
  loop invariant i - j >= 0;
  loop invariant i == \at(b, Pre) + 12;
  loop invariant p == n + 3*(j - i)*((j - i) + 2);
  loop invariant (j - i) >= 0;
  loop assigns v, j, p;
*/
while (1) {
      if (j>=i) {
          break;
      }
      v = v+2;
      j = j+1;
      v = v+4;
      p = p+v;
  }

}
