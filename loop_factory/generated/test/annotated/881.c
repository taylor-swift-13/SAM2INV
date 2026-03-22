int main1(int i){
  int qc, kt, r6z, xo;
  qc=i+10;
  kt=0;
  r6z=0;
  xo=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i,Pre) + (kt*(kt+1))/2;
  loop invariant xo == 7 - kt;
  loop invariant qc == \at(i,Pre) + 10;
  loop invariant r6z == kt*(15 - kt)/2;
  loop assigns i, kt, r6z, xo;
*/
while (kt<qc&&xo>0) {
      kt++;
      r6z = r6z + xo;
      i = i + kt;
      xo--;
  }
}