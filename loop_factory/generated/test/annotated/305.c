int main1(int z){
  int rz, mb, nkyb;
  rz=z;
  mb=0;
  nkyb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mb >= 0;
  loop invariant nkyb == 0;
  loop invariant mb <= rz || rz < 0;
  loop invariant z == rz * (mb + 1);
  loop invariant rz == \at(z, Pre);
  loop assigns mb, z, nkyb;
*/
while (mb<rz) {
      if (mb%2==0) {
          if (nkyb>0) {
              nkyb -= 1;
              nkyb++;
          }
      }
      else {
          if (nkyb>0) {
              nkyb -= 1;
              nkyb++;
          }
      }
      mb = mb + 1;
      z += rz;
  }
}