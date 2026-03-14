int main1(int d){
  int ctof, d47, rj, z, aky, om;

  ctof=d;
  d47=0;
  rj=0;
  z=0;
  aky=8;
  om=-6;

  while (1) {
      if (!(rj<ctof&&aky>0)) {
          break;
      }
      rj++;
      z = z + aky;
      aky -= 1;
      om = om + d47;
  }

}
