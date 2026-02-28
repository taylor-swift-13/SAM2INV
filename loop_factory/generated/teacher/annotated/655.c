int main1(int m,int p){
  int q, v, n, z, e, l;

  q=31;
  v=1;
  n=v;
  z=p;
  e=q;
  l=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 1;
  loop invariant e == 31;
  loop invariant n % 3 == 1;
  loop invariant n >= 1;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == 31;
  loop invariant ((n - 1) % 3) == 0;
  loop invariant (n - 1) % 3 == 0;
  loop invariant ((z == p) || (z == e));
  loop invariant v <= q;
  loop invariant 1 <= v;

  loop invariant z <= p;
  loop assigns n, z;
*/
while (v<=q-1) {
      n = n+3;
      if (e<=z) {
          z = e;
      }
  }

}
