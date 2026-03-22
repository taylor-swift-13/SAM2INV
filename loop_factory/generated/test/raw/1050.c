int main1(){
  int ey, q, t4, fj, jxh;

  ey=1-6;
  q=ey;
  t4=0;
  fj=0;
  jxh=5;

  while (fj<=ey-1) {
      t4 = t4 + 1;
      fj++;
      jxh = jxh+ey-q;
      jxh = jxh + q;
  }

  while (1) {
      if (!(t4<q)) {
          break;
      }
      t4 = t4 + 1;
      fj++;
      fj = fj*2;
  }

}
