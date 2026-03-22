int main1(int j){
  int gwhv, ma, ftjn, udj, qt2y, kue;

  gwhv=j+11;
  ma=0;
  ftjn=0;
  udj=0;
  qt2y=(j%18)+5;
  kue=gwhv;

  while (1) {
      if (!(qt2y>=1)) {
          break;
      }
      udj = udj+j*j;
      ma = ma+j*j;
      qt2y -= 1;
      ftjn = ftjn+j*j;
      kue = kue+(ftjn%6);
  }

  while (qt2y>gwhv) {
      qt2y -= gwhv;
      gwhv = gwhv + 1;
      j += gwhv;
      udj = udj*2;
      j = j + udj;
  }

}
