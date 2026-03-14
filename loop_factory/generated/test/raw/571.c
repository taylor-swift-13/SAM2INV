int main1(){
  int ixv, sg, x, oky;

  ixv=(1%16)+17;
  sg=0;
  x=0;
  oky=0;

  while (x<ixv) {
      x = x + 1;
      sg = (sg+1)%4;
      oky += x;
      oky = oky + 1;
  }

}
