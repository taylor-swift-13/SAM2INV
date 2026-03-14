int main1(){
  int evu, f0c, yhe, ci, e8;

  evu=1-10;
  f0c=0;
  yhe=0;
  ci=0;
  e8=0;

  while (1) {
      if (!(yhe<=evu-1)) {
          break;
      }
      ci += yhe;
      e8 = e8 + f0c;
      yhe += 1;
  }

  while (1) {
      if (!(evu<e8)) {
          break;
      }
      evu += 8;
  }

}
