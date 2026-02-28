int main1(int a,int b,int k,int n){
  int v, g, t, p, y, i;

  v=26;
  g=0;
  t=0;
  p=n;
  y=g;
  i=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 2*(\at(n,Pre) - p);
  loop invariant (y == 0) || (y == i);
  loop invariant t <= v + 1;

  loop invariant p <= n;
  loop invariant 2*p + t == 2*n;
  loop invariant t <= v;
  loop invariant i == b;
  loop invariant b == \at(b, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == n - t/2;
  loop invariant t % 2 == 0;
  loop invariant y == 0 || y == i;
  loop invariant t == 2*(n - p);

  loop invariant (2*p + t == 2*n) &&
                 (t >= 0) &&
                 (t <= v) &&
                 (p <= n) &&
                 (p >= n - v);
  loop invariant (p == n - (t / 2));
  loop assigns p, t, y;
*/
while (t<v) {
      t = t+1;
      if (i<=y) {
          y = i;
      }
      t = t+1;
      p = p-1;
  }

}
