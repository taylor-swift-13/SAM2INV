int main1(int y,int t){
  int qp, gw2, p1, ha;

  qp=40;
  gw2=0;
  p1=0;
  ha=1;

  while (p1>0&&ha<=qp) {
      if (p1>ha) {
          p1 = p1 - ha;
      }
      else {
          p1 = 0;
      }
      p1 += 1;
      ha = ha + 1;
      gw2 += 1;
  }

}
