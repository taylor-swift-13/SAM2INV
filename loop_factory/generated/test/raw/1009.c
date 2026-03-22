int main1(){
  int xzb, qx, rg9, ur;

  xzb=(1%17)+12;
  qx=0;
  rg9=2;
  ur=1;

  while (qx<xzb) {
      if (rg9>=11) {
          ur = -1;
      }
      if (!(rg9>2)) {
          ur = 1;
      }
      qx += 1;
      rg9 = rg9 + ur;
  }

}
