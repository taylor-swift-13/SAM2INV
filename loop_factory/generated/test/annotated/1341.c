int main1(){
  int z, o1, qcz;
  z=0;
  o1=(1%28)+10;
  qcz=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o1 + z*(z-1)/2 == 11;
  loop invariant qcz - z*(z+1)/2 == -8;
  loop invariant z >= 0;
  loop assigns o1, z, qcz;
*/
while (1) {
      if (!(o1>z)) {
          break;
      }
      o1 -= z;
      z += 1;
      qcz += z;
  }
}