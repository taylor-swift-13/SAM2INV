int main1(){
  int bw, y0vp, p3, vug;

  bw=0;
  y0vp=-19067;
  p3=1+5;
  vug=bw;

  while (1) {
      if (!(y0vp<=-5)) {
          break;
      }
      y0vp = y0vp+p3+3;
      p3++;
      vug = vug + p3;
  }

}
