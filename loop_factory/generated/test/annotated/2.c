int main1(int m,int u,int v){
  int u4, qn, t8, z;
  u4=(v%24)+8;
  qn=2;
  t8=v;
  z=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qn == 2;
  loop invariant u4 == (\at(v, Pre) % 24) + 8;
  loop invariant m == \at(m, Pre) + 3*(z + 6);
  loop invariant z >= -6;
  loop invariant u == \at(u, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant (m - \at(m, Pre)) == 3 * (z + 6);
  loop invariant (z == -6) ==> (t8 == v);
  loop invariant (z > -6) ==> (t8 == z*z);
  loop invariant u4 == (v % 24) + 8;
  loop invariant m >= \at(m,Pre);
  loop assigns z, t8, m;
*/
while (1) {
      if (!(qn+2<=u4)) {
          break;
      }
      z += 1;
      t8 = z*z;
      m = m + qn;
      m++;
  }
}