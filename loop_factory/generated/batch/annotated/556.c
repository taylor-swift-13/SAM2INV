int main1(int p,int q){
  int l, y, s, n;

  l=68;
  y=3;
  s=y;
  n=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == y;
  loop invariant s >= 3;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == 3*s - 6 + ((s-3)*(s-2))/2;
  loop invariant l == 68;
  loop invariant n == s*(s+1)/2 - 3;
  loop invariant y == s;
  loop invariant n == (s*s + s - 6) / 2;
  loop assigns s, n, y;
*/
while (1) {
      s = s+1;
      n = n+s;
      y = y+1;
  }

}
