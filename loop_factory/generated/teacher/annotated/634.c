int main1(int a,int n){
  int k, b, g, y, m, v;

  k=n;
  b=0;
  g=b;
  y=n;
  m=k;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant g == 0;
  loop invariant n == \at(n, Pre);
  loop invariant k == n;
  loop invariant y == n;
  loop invariant y == \at(n, Pre);
  loop assigns y;
*/
while (1) {
      y = y+g;
  }

}
