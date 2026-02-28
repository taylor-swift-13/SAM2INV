int main1(int p,int q){
  int l, y, s, n;

  l=68;
  y=3;
  s=y;
  n=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 68;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant s >= 3;
  loop invariant s <= l;
  loop invariant n >= 3;
  loop invariant (n + s + 2) % 2 == 0;
  loop invariant n % 2 == s % 2;
  loop assigns s, n;
*/
while (s<l) {
      if (s<l) {
          s = s+1;
      }
      n = n+n;
      n = n+s;
  }

}
