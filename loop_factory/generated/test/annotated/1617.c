int main1(int i){
  int txc, zfyq, x4o, d2v;
  txc=i+25;
  zfyq=0;
  x4o=i;
  d2v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x4o == \at(i, Pre);
  loop invariant txc == \at(i, Pre) + 25;
  loop invariant (zfyq == 0) || (zfyq == txc);
  loop invariant d2v == 0;
  loop assigns d2v, i, zfyq;
*/
while (1) {
      if (!(zfyq<=txc-1)) {
          break;
      }
      d2v = d2v+x4o*zfyq;
      i = i + i;
      zfyq = txc;
  }
}