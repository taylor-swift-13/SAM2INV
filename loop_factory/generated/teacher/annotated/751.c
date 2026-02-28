int main1(int a,int m,int n,int p){
  int d, g, e, v, u;

  d=26;
  g=d;
  e=m;
  v=p;
  u=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == p;
  loop invariant v == p;
  loop invariant g == 26;
  loop invariant d == 26;
  loop invariant e >= m;
  loop invariant (e - m) % 5 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant g >= 1;
  loop invariant g <= 26;
  loop invariant v == \at(p,Pre);
  loop invariant e >= \at(m,Pre);
  loop invariant (e - \at(m,Pre)) % 5 == 0;
  loop invariant u == \at(p,Pre);
  loop assigns v, e;
*/
while (g>=1) {
      if (u<=v) {
          v = u;
      }
      e = e+1;
      e = e+4;
  }

}
