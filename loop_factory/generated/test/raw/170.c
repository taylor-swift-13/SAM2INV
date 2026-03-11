int main1(){
  int w5m, gw, s2g, j2a;

  w5m=(1%18)+17;
  gw=-1;
  s2g=0;
  j2a=1;

  while (gw<w5m) {
      if (!(s2g<8)) {
          j2a = -1;
      }
      if (s2g<=0) {
          j2a = 1;
      }
      gw = gw + 1;
      s2g = s2g + j2a;
  }

}
