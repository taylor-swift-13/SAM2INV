int main1(){
  int h, yh, u2, c7sn, f1;

  h=9;
  yh=3;
  u2=0;
  c7sn=-5;
  f1=h;

  while (u2<h) {
      c7sn = u2;
      u2 += 1;
      f1 = f1 + u2;
  }

  while (yh<=f1-1) {
      yh = yh + 1;
      c7sn++;
      if ((h%6)==0) {
          c7sn += 6;
      }
  }

}
