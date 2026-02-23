int main1(int n,int p){
  int l, d, y;

  l=68;
  d=l;
  y=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 68;
  loop invariant d >= 0;
  loop invariant d <= 68;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant y == -6 || y == n - (-4);
  loop invariant 0 <= d;
  loop invariant d <= l;
  loop invariant (y == n + 4) || (d == l);
  loop invariant (y == -6) || (y == n + 4);
  loop invariant y == -6 || y == n + 4;
  loop invariant y == n + 4 || y == -6;
  loop assigns d, y;
*/
while (d>0) {
      y = n-(-4);
      d = d-1;
  }

}
