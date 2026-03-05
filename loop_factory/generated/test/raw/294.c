int main1(int v,int n){
  int vy, vd, b6, u;

  vy=n;
  vd=0;
  b6=3;
  u=1;

  while (vd<vy) {
      if (b6>=11) {
          u = -1;
      }
      if (b6<=3) {
          u = 1;
      }
      b6 = b6 + u;
      vd += 1;
      n += b6;
  }

}
