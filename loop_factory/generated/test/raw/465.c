int main1(int r,int a){
  int xb, zp, f, bkp;

  xb=r;
  zp=0;
  f=0;
  bkp=0;

  while (1) {
      if (!(bkp<xb)) {
          break;
      }
      bkp += 1;
      f += r;
      r = r+xb-zp;
  }

  while (1) {
      zp = zp+r+a;
      f = f + 1;
      if (f>=bkp) {
          break;
      }
  }

}
