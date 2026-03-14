int main1(){
  int ry, k, trl, ys, gge, xds;

  ry=1+15;
  k=4;
  trl=ry;
  ys=0;
  gge=0;
  xds=ry;

  while (k+1<=ry) {
      ys += trl;
      gge += ys;
      xds = xds+(ys%7);
      ry = (k+1)-1;
  }

  while (1) {
      if (!(xds-6>=0)) {
          break;
      }
      gge = gge + k;
      ys = ys + xds;
      k += 2;
      xds += 1;
  }

}
