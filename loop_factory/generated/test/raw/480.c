int main1(){
  int oy9, bb, ic, nac, b9v, kzs;

  oy9=(1%37)+16;
  bb=oy9+6;
  ic=0;
  nac=(1%28)+10;
  b9v=bb;
  kzs=oy9;

  while (1) {
      if (!(nac>ic)) {
          break;
      }
      nac -= ic;
      ic = ic + 1;
      kzs = kzs+(ic%7);
      b9v += bb;
      kzs = kzs*kzs;
  }

  while (1) {
      if (!(kzs<=ic-1)) {
          break;
      }
      kzs = kzs*4;
  }

}
