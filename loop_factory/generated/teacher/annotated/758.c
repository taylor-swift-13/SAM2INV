int main1(int a,int n,int p,int q){
  int x, t, v, y, j;

  x=59;
  t=1;
  v=n;
  y=n;
  j=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((v - y) == 0) || ((v - y) == 3);
  loop invariant y <= v;
  loop invariant v >= \at(n, Pre);
  loop invariant ((v - \at(n, Pre)) % 3) == 0;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v - y == 0) || (v - y == 3);
  loop invariant (v - n) % 3 == 0;
  loop invariant v >= n;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant y >= \at(n, Pre);
  loop invariant (y == v) || (y == v - 3);
  loop assigns y, v;
*/
while (1) {
      y = v;
      v = v+2;
      v = v+1;
  }

}
