int main1(){
  int d7, ccm, yi, rm, uy, l;

  d7=1+24;
  ccm=0;
  yi=-3;
  rm=ccm;
  uy=d7;
  l=d7;

  while (ccm < d7) {
      ccm++;
      rm += uy;
      l = l + ccm;
      yi += uy;
  }

}
