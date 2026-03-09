int main1(){
  int vu, acc, p6, aqq, ks;

  vu=(1%8)+5;
  acc=0;
  p6=0;
  aqq=0;
  ks=7;

  while (p6<vu&&ks>0) {
      p6++;
      aqq += ks;
      ks--;
      aqq = aqq + acc;
  }

}
