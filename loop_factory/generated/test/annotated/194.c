int main1(int l,int u){
  int p2n;
  p2n=-6620;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(l, Pre);
  loop invariant p2n % 2 == 0;
  loop invariant p2n <= -6620;
  loop invariant u - \at(u, Pre) == 2*(p2n + 6620);
  loop assigns p2n, u;
*/
while (p2n+2<0) {
      p2n = p2n+p2n-3;
      p2n = p2n + 3;
      u += p2n;
  }
}