int main1(int d,int a){
  int ra5, mng2, u, yh, e;

  ra5=18;
  mng2=0;
  u=15;
  yh=1;
  e=0;

  for (; u>0&&yh<=ra5; mng2 = mng2 + 1) {
      if (u>yh) {
          u = u - yh;
      }
      else {
          u = 0;
      }
      e += 1;
      yh = yh + 1;
  }

}
