int main1(int y){
  int w, yg, zg, ye0, p6b;

  w=52;
  yg=w;
  zg=w;
  ye0=0;
  p6b=16;

  while (yg>=1) {
      ye0 = ye0 + zg;
      yg = 0;
  }

  while (1) {
      if (!(yg<=p6b-1)) {
          break;
      }
      w = w + y;
      yg += 1;
  }

}
