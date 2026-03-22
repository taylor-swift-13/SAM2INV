int main1(){
  int zn, hp8, e3q, ns7u, zz92, z;
  zn=(1%16)+12;
  hp8=0;
  e3q=0;
  ns7u=1;
  zz92=6;
  z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= z <= zn + 1;
  loop invariant 0 <= e3q;
  loop invariant 0 <= ns7u;
  loop invariant zz92 == 6 * (z + 1);
  loop invariant zn == 13;
  loop invariant hp8 == 0;
  loop assigns e3q, ns7u, z, zz92;
*/
while (z<=zn) {
      z += 1;
      e3q = e3q + ns7u;
      ns7u = ns7u + zz92;
      zz92 += 6;
      ns7u = ns7u*ns7u;
      e3q += hp8;
  }
}