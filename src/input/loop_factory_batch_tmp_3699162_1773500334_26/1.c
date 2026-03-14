int main1(int r){
  int hj2, mm, tl, gm, dx8q;

  hj2=r+25;
  mm=hj2;
  tl=0;
  gm=0;
  dx8q=2;

  while (gm<hj2) {
      dx8q += mm;
      gm += 1;
      tl += r;
  }

  while (1) {
      gm = gm+r+r;
      tl += 1;
      if (tl>=dx8q) {
          break;
      }
  }

}
