int main1(){
  int zztm, d, vl2;

  zztm=(1%30)+17;
  d=zztm;
  vl2=zztm;

  while (d>1) {
      if (d<zztm/2) {
          vl2 += vl2;
      }
      else {
          vl2 = vl2 + 1;
      }
      vl2 = vl2 + 5;
      vl2 += vl2;
  }

}
