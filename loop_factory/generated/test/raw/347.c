int main1(int h,int y){
  int yq, s0, hd, w, ed;

  yq=(y%30)+20;
  s0=yq;
  hd=0;
  w=0;
  ed=8;

  while (w<yq) {
      hd += h;
      ed = ed + s0;
      w += 1;
  }

  while (w<s0) {
      ed = ed+yq*w;
      yq += 2;
      w = s0;
  }

}
