int main1(int o,int p){
  int mhr, ssqh, sc3, bey;

  mhr=o;
  ssqh=0;
  sc3=1;
  bey=1;

  while (1) {
      if (!(sc3<=mhr)) {
          break;
      }
      ssqh = ssqh + 1;
      bey += 2;
      sc3 += bey;
      o = o+(sc3%6);
  }

}
