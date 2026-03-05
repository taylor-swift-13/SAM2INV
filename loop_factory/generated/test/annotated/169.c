int main1(){
  int vw, t8, vz;
  vw=1+18;
  t8=2;
  vz=t8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vw == 1 + 18;
  loop invariant vz <= 2*vw;
  loop invariant vz % 2 == 0;
  loop invariant vz >= 2;
  loop assigns vz;
*/
while (vz<=vw) {
      vz += vz;
  }
}