int main1(int r,int o){
  int h, ek, d, dvu;

  h=r+22;
  ek=0;
  d=2;
  dvu=1;

  while (ek<h) {
      if (d>=6) {
          dvu = -1;
      }
      if (!(d>2)) {
          dvu = 1;
      }
      d = d + dvu;
      ek++;
  }

}
