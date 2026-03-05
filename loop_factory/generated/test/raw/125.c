int main1(int h,int a){
  int fk30, sden, zs1, dn;

  fk30=46;
  sden=fk30;
  zs1=0;
  dn=1;

  while (sden<fk30) {
      if (zs1>=4) {
          dn = -1;
      }
      if (zs1<=0) {
          dn = 1;
      }
      zs1 += dn;
      sden = sden + 1;
      h += dn;
  }

}
