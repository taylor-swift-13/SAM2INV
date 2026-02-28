int main1(int k,int m,int n,int p){
  int r, v, t, a, u, f, h;

  r=k;
  v=0;
  t=n;
  a=-4;
  u=r;
  f=k;
  h=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == k;

  loop invariant t >= n;
  loop invariant (a <= -4) || (a <= u);
  loop invariant r == k;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre));
  loop invariant (a == -4) || (a == k);
  loop invariant a <= -4;
  loop invariant a == -4 || a == k;
  loop invariant a <= -4 && (a == -4 || a == k);
  loop assigns a, t;
*/
while (1) {
      if (u<=a) {
          a = u;
      }
      t = t+1;
  }

}
