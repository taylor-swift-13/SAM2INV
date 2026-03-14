int main1(int q,int b){
  int tt, r72, u, m, iy, kh;

  tt=50;
  r72=3;
  u=0;
  m=-2;
  iy=-6;
  kh=q;

  while (1) {
      if (!(m<tt)) {
          break;
      }
      m++;
      u = u + q;
      b = b + u;
      iy = iy*2;
  }

  while (1) {
      if (!(tt<kh)) {
          break;
      }
      m = m + u;
      iy = iy + u;
      r72 = r72 + q;
      tt++;
  }

}
