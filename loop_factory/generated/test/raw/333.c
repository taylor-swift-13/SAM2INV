int main1(){
  int hib, yh, wj, yl, jn, mc;

  hib=1;
  yh=0;
  wj=0;
  yl=0;
  jn=6;
  mc=hib;

  while (yl<hib) {
      wj = wj + 1;
      jn += 2;
      yl++;
      mc = mc+(wj%3);
  }

  while (yl>0) {
      if (yl%2==0) {
          yh = yh + hib;
      }
      else {
          yh = yh+hib+1;
      }
      yl = 0;
  }

}
