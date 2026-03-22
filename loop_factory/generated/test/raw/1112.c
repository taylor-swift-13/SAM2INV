int main1(int a){
  int g, vw, g3, pbhy, u, d;

  g=a*3;
  vw=g+3;
  g3=3;
  pbhy=-4;
  u=a;
  d=a;

  while (pbhy<=g-1) {
      g3 = g3 + a;
      u = u + vw;
      pbhy = pbhy + 1;
  }

  while (vw<g) {
      vw = vw + 1;
      d = d + a;
      pbhy = pbhy+(vw%6);
  }

}
