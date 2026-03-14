int main1(int g){
  int id, cr6, u, xax, u817;

  id=25;
  cr6=2;
  u=0;
  xax=0;
  u817=0;

  while (xax<id) {
      u = u + g;
      u817++;
      xax++;
      g = g+(xax%7);
  }

  while (id<xax) {
      u817 = u817 + g;
      id++;
      cr6 = cr6 + u817;
      cr6 = cr6*2;
  }

}
