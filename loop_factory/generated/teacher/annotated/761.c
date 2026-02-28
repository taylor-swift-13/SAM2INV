int main1(int a,int m,int n,int p){
  int h, b, v, f, u, i, d, q;

  h=(m%28)+10;
  b=0;
  v=1;
  f=m;
  u=m;
  i=-2;
  d=h;
  q=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 1;
  loop invariant (v - 1) % 5 == 0;
  loop invariant f == m + ((v - 1) * (v - 2)) / 10;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v >= 1);
  loop invariant ((v - 1) % 5 == 0);
  loop invariant (f >= m);
  loop invariant (m == \at(m, Pre));
  loop invariant (a == \at(a, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant 10*(f - m) == (v - 1)*(v - 2);
  loop invariant f >= m;
  loop invariant 10*f - v*v + 3*v == 10*\at(m,Pre) + 2;
  loop invariant f >= \at(m,Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v % 5 == 1;
  loop invariant f == \at(m, Pre) + ((v - 1) * (v - 2)) / 10;
  loop assigns v, f;
*/
while (1) {
      v = v+1;
      f = f+v;
      v = v+4;
  }

}
