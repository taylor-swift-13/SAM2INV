int main1(int r,int d){
  int g6u, i4, vq, ges7, s2, k6, n, t6, xy;

  g6u=r-10;
  i4=0;
  vq=0;
  ges7=20;
  s2=r;
  k6=20;
  n=-8;
  t6=r;
  xy=r+4;

  while (vq<=g6u-1) {
      vq = vq + 1;
      if (s2<=ges7) {
          ges7 = s2;
      }
      if (n+7<g6u) {
          n = n%2;
      }
      k6 = k6 + vq;
      xy = xy+(ges7%7);
      t6 = t6+vq-vq;
      r = r+(vq%9);
      s2 = s2+ges7-ges7;
      k6 = k6*k6;
      s2 = s2 + i4;
      n = n+s2*k6;
  }

}
