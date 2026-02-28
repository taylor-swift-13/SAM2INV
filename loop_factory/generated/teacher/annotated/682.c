int main1(int a,int n,int p,int q){
  int x, t, v, m, j, h, s, z;

  x=q+19;
  t=0;
  v=n;
  m=n;
  j=4;
  h=x;
  s=t;
  z=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == n + t*(t-1)/2;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t >= 0;
  loop invariant 2*(v - n) == t*(t - 1);
  loop invariant x == \at(q, Pre) + 19;
  loop invariant v == \at(n,Pre) + (t*(t-1))/2;
  loop invariant (((t == 0) ==> m == n) && ((t >= 1) ==> m >= 0));
  loop assigns v, m, t;
*/
while (1) {
      v = v+t;
      m = m*m;
      t = t+1;
  }

}
