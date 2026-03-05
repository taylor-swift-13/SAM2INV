int main1(){
  int xssf, yx, lctw;

  xssf=1+8;
  yx=0;
  lctw=0;

  while (yx<xssf) {
      lctw++;
      if (lctw>=4) {
          lctw -= 4;
          lctw++;
      }
      yx++;
  }

}
