int main1(){
  int h4, zp, xxz, a1, pz;

  h4=34;
  zp=1;
  xxz=h4;
  a1=0;
  pz=zp;

  while (zp<h4) {
      xxz = xxz*2;
      a1 += xxz;
      pz = pz%8;
      zp = zp + 1;
  }

}
