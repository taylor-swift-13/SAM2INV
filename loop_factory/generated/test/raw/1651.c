int main1(int f){
  int bg, gw, d8, p56;

  bg=f+24;
  gw=0;
  d8=0;
  p56=4;

  while (1) {
      if (!(gw<bg&&p56>0)) {
          break;
      }
      d8 = d8 + p56;
      gw = gw + 1;
      p56--;
  }

}
