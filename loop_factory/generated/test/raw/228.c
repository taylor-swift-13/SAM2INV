int main1(int l,int z){
  int gw, s9, e2, vf, h7, d5;

  gw=z;
  s9=gw+3;
  e2=0;
  vf=0;
  h7=l;
  d5=gw;

  while (vf<gw) {
      vf++;
      e2 += l;
      h7 = h7 + e2;
      d5 = d5 + 3;
  }

  while (vf<d5) {
      gw += 2;
      vf++;
      s9 += l;
      e2 += s9;
  }

}
