int main1(int z){
  int ixrz, qfl, d7o, tju;
  ixrz=z;
  qfl=0;
  d7o=1;
  tju=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qfl;
  loop invariant z == \at(z,Pre) + qfl * (qfl + 1) / 2;
  loop invariant (ixrz > 0) ==> (0 <= qfl && qfl <= ixrz);
  loop invariant ((qfl == 0) ==> (d7o == 1));
  loop invariant ((qfl > 0) ==> (d7o == qfl - 1));
  loop assigns z, qfl, d7o;
*/
while (1) {
      if (!(qfl<=ixrz-1)) {
          break;
      }
      if (tju<ixrz) {
          d7o = qfl;
      }
      qfl += 1;
      z = z + qfl;
  }
}