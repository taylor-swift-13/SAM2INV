int main1(int f){
  int sif, h06, qm;
  sif=19;
  h06=sif;
  qm=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h06 == 19;
  loop invariant sif == 19;
  loop invariant qm >= 2;
  loop invariant 3*(f - \at(f, Pre)) == sif*(qm - 2);
  loop invariant f >= \at(f, Pre);
  loop invariant qm % 3 == 2;
  loop assigns f, qm;
*/
while (h06>0) {
      qm = qm + 3;
      f += sif;
  }
}