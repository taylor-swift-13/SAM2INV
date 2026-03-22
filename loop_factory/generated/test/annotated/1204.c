int main1(){
  int qg, z, m6fj, ihv, oim, i, s8, a2;
  qg=1-2;
  z=qg;
  m6fj=(1%35)+15;
  ihv=(1%35)+15;
  oim=1;
  i=0;
  s8=0;
  a2=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m6fj >= 0;
  loop invariant ihv >= 0;
  loop invariant z == -1;
  loop invariant qg == -1;
  loop invariant (m6fj + ihv) <= 32;
  loop assigns m6fj, oim, s8, ihv, i, a2;
*/
while (m6fj!=ihv) {
      if (m6fj>ihv) {
          m6fj = m6fj - ihv;
          oim = oim - i;
          s8 = s8 - a2;
      }
      else {
          ihv = ihv - m6fj;
          i = i - oim;
          a2 = a2 - s8;
      }
      oim += z;
  }
}