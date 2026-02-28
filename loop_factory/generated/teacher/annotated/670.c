int main1(int a,int b,int m,int p){
  int r, d, c, v, u, o;

  r=b-10;
  d=0;
  c=-8;
  v=m;
  u=a;
  o=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant u == a;
  loop invariant (v == m) || (v == a);
  loop invariant c >= -8;
  loop invariant r == b - 10;
  loop invariant v <= m;

  loop invariant (v == m) || (v == u);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == \at(a,Pre);
  loop invariant v <= \at(m,Pre);
  loop invariant (v == \at(m,Pre)) || (v == u);
  loop assigns v, c;
*/
while (1) {
      if (u<=v) {
          v = u;
      }
      c = c+1;
  }

}
