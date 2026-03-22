int main1(){
  int yw, ogwq, xc, fbye, bl, e;

  yw=1;
  ogwq=(1%60)+60;
  xc=(1%9)+2;
  fbye=0;
  bl=0;
  e=yw;

  while (ogwq>xc*fbye+bl) {
      if (bl==xc-1) {
          bl = 0;
          fbye += 1;
      }
      else {
          bl += 1;
      }
      e = e+fbye-fbye;
  }

}
