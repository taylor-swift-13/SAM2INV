int main1(int a,int k,int p,int q){
  int r, z, v, j, n, m, h, w;

  r=21;
  z=0;
  v=0;
  j=r;
  n=a;
  m=-3;
  h=8;
  w=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant v <= r;
  loop invariant (n == a) || (n == m);
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == 21;
  loop invariant m == -3;
  loop invariant 0 <= v;
  loop invariant n == a || n == m;
  loop invariant (n == m) || (n == \at(a,Pre));
  loop invariant (v == 0) ==> (n == \at(a, Pre));
  loop invariant (v > 0) ==> ( (\at(a, Pre) >= -3 && n == -3) || ( \at(a, Pre) < -3 && n == \at(a, Pre) ) );
  loop assigns v, n;
*/
while (v<r) {
      v = v+1;
      if (m<=n) {
          n = m;
      }
  }

}
