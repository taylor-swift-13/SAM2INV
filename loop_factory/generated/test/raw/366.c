int main1(int f){
  int j, yl, tf, ck, fdp, y6u;

  j=f;
  yl=j;
  tf=0;
  ck=(f%28)+10;
  fdp=j;
  y6u=7;

  while (1) {
      if (!(ck>tf)) {
          break;
      }
      ck -= tf;
      tf += 1;
      fdp += tf;
      f = f+(ck%3);
      y6u = y6u+j-yl;
  }

  for (; j>5; j -= 6) {
  }

}
