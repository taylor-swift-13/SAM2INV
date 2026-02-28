int main1(int a,int m){
  int n, y, v, o;

  n=38;
  y=0;
  v=y;
  o=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant y % 2 == 0;
  loop invariant y <= n;
  loop invariant n == 38;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (y % 2) == 0;
  loop invariant 0 <= y;
  loop assigns v, y;
*/
while (y<=n-2) {
      v = v*3;
      y = y+2;
  }

}
