int main1(){
  int gf, uce, lh, oc;

  gf=0;
  uce=0;
  lh=(1%28)+10;
  oc=gf;

  while (lh>uce) {
      lh = lh - uce;
      uce += 1;
      oc = oc + gf;
      oc = oc*4+1;
  }

}
