int main1(int h){
  int d, u9p, mz, el2k, yy33, gil;

  d=h;
  u9p=0;
  mz=45;
  el2k=0;
  yy33=1;
  gil=0;

  for (; mz>0&&u9p<d; u9p++) {
      if (mz<=yy33) {
          gil = mz;
      }
      else {
          gil = yy33;
      }
      yy33 += 1;
      mz -= gil;
      el2k += gil;
  }

}
