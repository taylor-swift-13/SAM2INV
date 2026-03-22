int main1(int r,int p){
  int afs, t03, nwc, hi, mq;
  afs=41;
  t03=-6;
  nwc=0;
  hi=afs;
  mq=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hi == 41 + 4*(mq - 6);
  loop invariant nwc == 2*(mq - 6)*(mq - 6) + 39*(mq - 6);
  loop invariant 6*t03 == 4*mq*mq*mq + 39*mq*mq - 1015*mq + 3786;
  loop invariant r == \at(r, Pre) + t03 + 6 + (mq - 6) * (2*(mq - 6) + 39) + (mq - 6) * p;
  loop assigns r, t03, nwc, mq, hi;
*/
while (mq<=afs) {
      t03 += nwc;
      nwc = nwc + hi;
      mq = mq + 1;
      r += nwc;
      hi += 4;
      r += p;
  }
}