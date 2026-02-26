int main1(int m,int n){
  int l, t, x;

  l=m;
  t=0;
  x=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == m;
  loop invariant t == 0;
  loop invariant x >= 5;

  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant x >= 0;
  loop invariant x > 0;
  loop assigns x;
*/
while (1) {
      x = x+4;
      x = x*x;
      if (t+3<=n+l) {
          x = x*x;
      }
  }

}
