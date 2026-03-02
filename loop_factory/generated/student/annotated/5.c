int main1(int m,int p){
  int c, n, s;

  c=p-7;
  n=2;
  s=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant n == 2;

  loop invariant m == \at(m, Pre);

  loop invariant s >= 2;
  loop invariant c == \at(p, Pre) - 7;
  loop invariant p == \at(p, Pre);

  loop assigns s;
*/
while (1) {
      s = s+3;
      s = s*s;
      if (n+3<=n+c) {
          s = s*s+s;
      }
  }

}
