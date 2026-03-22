int main1(int r,int p){
  int afs, t03, nwc, hi, mq;

  afs=41;
  t03=-6;
  nwc=0;
  hi=afs;
  mq=6;

  while (mq<=afs) {
      t03 += nwc;
      nwc = nwc + hi;
      mq = mq + 1;
      r += nwc;
      hi += 4;
      r += p;
  }

}
