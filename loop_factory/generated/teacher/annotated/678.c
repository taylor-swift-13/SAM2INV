int main1(int k,int m,int p,int q){
  int t, x, y, v, l, r;

  t=(q%17)+11;
  x=0;
  y=p;
  v=p;
  l=-3;
  r=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t == (q % 17) + 11;
  loop invariant y >= p;
  loop invariant l == -3;
  loop invariant t == ((\at(q,Pre)) % 17) + 11;
  loop invariant (v == \at(p,Pre)) || (v == l);
  loop invariant y >= \at(p,Pre);
  loop invariant (v == p) || (v == l);
  loop invariant v <= \at(p,Pre);
  loop invariant y >= p && ((v == p) || (v == l));
  loop assigns y, v;
*/
while (1) {
      y = y+1;
      if (l<=v) {
          v = l;
      }
  }

}
