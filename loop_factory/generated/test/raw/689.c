int main1(int u,int g){
  int jd4, s, nc, x3, qnz, u4, ybn;

  jd4=56;
  s=jd4;
  nc=7;
  x3=7;
  qnz=0;
  u4=7;
  ybn=0;

  while (s<jd4) {
      if (!(!(s%3==0))) {
          if (nc>0) {
              nc = nc - 1;
              qnz = qnz + 1;
          }
      }
      else {
          if (nc<u4) {
              nc += 1;
              x3 = x3 + 1;
          }
      }
      ybn += 1;
      s++;
  }

}
