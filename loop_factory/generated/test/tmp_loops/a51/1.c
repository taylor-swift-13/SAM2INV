int main1(int d){
  int h3, t, zcm, ktg, y1;

  h3=d+17;
  t=0;
  zcm=-2;
  ktg=d*4;
  y1=h3;

  while (zcm<=h3-1) {
      ktg = zcm+6;
      zcm = zcm + 1;
      y1 = y1 + h3;
  }

  while (1) {
      zcm = zcm + 1;
      y1 += 1;
      if (y1>=t) {
          break;
      }
  }

}
