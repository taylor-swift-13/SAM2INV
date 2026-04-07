int main1(){
  int w, gb, mcnf, ild, hul;

  w=1;
  gb=0;
  mcnf=1;
  ild=6;
  hul=0;

  while (1) {
      if (!(hul<=w)) {
          break;
      }
      gb += mcnf;
      hul += 1;
      mcnf = mcnf + ild;
      ild += 2;
  }

}
