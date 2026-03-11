int main1(){
  int oai, r0, z, m2;
  oai=1;
  r0=0;
  z=6;
  m2=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 6;
  loop invariant 0 <= r0 <= oai;
  loop invariant z <= 6 + m2;
  loop invariant (z - 6 == 0) || (z - 6 == 1) || (z - 6 == m2);
  loop invariant z - r0*m2 == 6;
  loop assigns z, r0;
*/
while (r0<oai) {
      if (!(!(r0<oai/2))) {
          z += 1;
      }
      else {
          z = z + m2;
      }
      r0 = oai;
  }
}