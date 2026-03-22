int main1(int q){
  int zs, d, vq;
  zs=12;
  d=5;
  vq=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 5 + q * (vq + 2);
  loop invariant vq <= zs;
  loop invariant zs == 12;
  loop assigns d, vq;
*/
while (1) {
      if (!(vq<zs)) {
          break;
      }
      d = d + q;
      vq = vq + 1;
  }
}