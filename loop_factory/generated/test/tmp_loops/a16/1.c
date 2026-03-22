int main1(int b){
  int a8c0, j, zg, fa, gis, smh, yuh, a, opl;

  a8c0=200;
  j=a8c0;
  zg=0;
  fa=0;
  gis=0;
  smh=(b%18)+5;
  yuh=b;
  a=j;
  opl=0;

  while (smh>0) {
      fa = fa+b*b;
      zg = zg+b*b;
      gis = gis+b*b;
      smh -= 1;
      if (b+2<a8c0) {
          b = b*2;
      }
      if (smh*smh<=a8c0+5) {
          b = b%5;
      }
      opl = opl+(smh%2);
      yuh = yuh+(zg%7);
      a = a+(gis%2);
      yuh = yuh*3;
      a = a/3;
  }

}
