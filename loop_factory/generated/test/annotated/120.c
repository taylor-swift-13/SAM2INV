int main1(int z,int x){
  int pn2z, y, tr, ky;
  pn2z=141;
  y=-6;
  tr=0;
  ky=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tr;
  loop invariant tr <= pn2z;
  loop invariant (tr >= 1) ==> (ky == pn2z - tr);
  loop invariant (tr == 0) ==> (ky == -6);
  loop invariant z == \at(z,Pre) + tr * y;
  loop invariant ky <= pn2z - tr;
  loop assigns tr, z, ky;
*/
while (1) {
      if (!(tr<pn2z)) {
          break;
      }
      tr += 1;
      z = z + y;
      ky = pn2z-tr;
  }
}