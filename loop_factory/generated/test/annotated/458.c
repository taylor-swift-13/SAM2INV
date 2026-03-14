int main1(int n,int k){
  int fny, i9f, v6, t, p9;
  fny=n;
  i9f=0;
  v6=3;
  t=0;
  p9=k;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= 0;
  loop invariant n == \at(n, Pre) * (t + 1);
  loop invariant p9 == \at(k, Pre) + t*(t + 1)/2;
  loop invariant fny == \at(n, Pre);
  loop invariant i9f == 0;
  loop invariant p9 == k + t*(t+1)/2;
  loop assigns v6, t, n, p9;
*/
while (1) {
      if (!(t<fny)) {
          break;
      }
      v6 += n;
      t += 1;
      n = n+fny-i9f;
      p9 += t;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i9f >= 0;
  loop invariant i9f % 2 == 0;
  loop invariant p9 == k + t*(t+1)/2 + i9f/2;
  loop assigns i9f, v6, p9, n;
*/
while (1) {
      if (!(p9<=fny-1)) {
          break;
      }
      i9f += 2;
      v6 += n;
      p9++;
      n += t;
  }
}