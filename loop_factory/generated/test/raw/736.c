int main1(int d,int h){
  int yz, q6o, dt, gn;

  yz=(d%29)+16;
  q6o=0;
  dt=(d%28)+10;
  gn=-4;

  while (dt>q6o) {
      dt -= q6o;
      q6o = (1)+(q6o);
      gn = gn + yz;
  }

}
