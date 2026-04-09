int main1(int j){
  int dba, jz, ke, p, aus7;
  dba=j-10;
  jz=j;
  ke=0;
  p=jz;
  aus7=dba;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j,Pre) + (jz - \at(j,Pre)) * \at(j,Pre)
                            + ((jz - \at(j,Pre)) * (jz - \at(j,Pre) + 1)) / 2;
  loop invariant dba == \at(j,Pre) - 10;
  loop invariant p == \at(j,Pre);
  loop invariant aus7 == dba;
  loop invariant j - (jz*(jz + 1))/2 == (\at(j, Pre) - (\at(j, Pre) * (\at(j, Pre) + 1))/2);
  loop invariant jz >= \at(j, Pre);
  loop invariant ke == 0;
  loop invariant 2 * (j - \at(j,Pre)) == 2 * ( (jz - \at(j,Pre)) * \at(j,Pre) ) + ( (jz - \at(j,Pre)) * ( (jz - \at(j,Pre)) + 1 ) );
  loop invariant 2 * j == ((jz - \at(j,Pre) + 1) * (\at(j,Pre) + jz));
  loop invariant j >= \at(j,Pre);
  loop assigns j, jz;
*/
while (jz < dba && ke >= jz && p >= jz && aus7 >= jz) {
      jz = jz + 1;
      j += jz;
  }
}