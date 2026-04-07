int main1(){
  int j4, z, qk6, sn4;
  j4=13;
  z=0;
  qk6=j4;
  sn4=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sn4 == (3 * z);
  loop invariant qk6 == (j4 + (3 * z * (z - 1)) / 2);
  loop invariant ((0 <= z) && (z <= j4));
  loop invariant (j4 == 13);
  loop assigns qk6, z, sn4;
*/
while (z < j4) {
      qk6 = qk6 + sn4;
      z += 1;
      sn4 = sn4 + 3;
  }
}