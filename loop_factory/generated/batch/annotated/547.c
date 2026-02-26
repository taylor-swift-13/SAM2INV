int main1(int k,int m){
  int n, d, s, r;

  n=m;
  d=0;
  s=k;
  r=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == m;
  loop invariant d >= 0;
  loop invariant d <= n || n < 0;
  loop invariant s == r + d;
  loop invariant (n < 0) ==> (d == 0);
  loop invariant s - d == r;

  loop assigns s, d, r;
*/
while (1) {
      if (d>=n) {
          break;
      }
      s = s+1;
      d = d+1;
      s = s+r;
      r = r+r;
  }

}
