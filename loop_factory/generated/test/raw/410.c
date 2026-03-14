int main1(int h){
  int zb, ld, iwf, rp, qtr, nbk;

  zb=h-7;
  ld=0;
  iwf=43;
  rp=0;
  qtr=1;
  nbk=0;

  while (1) {
      if (!(iwf>0&&ld<zb)) {
          break;
      }
      if (iwf<=qtr) {
          nbk = iwf;
      }
      else {
          nbk = qtr;
      }
      qtr++;
      ld++;
      iwf = iwf - nbk;
      rp = rp + nbk;
  }

}
