int main123(int w,int v){
  int j5, x4, xm, fc, n33;

  j5=(w%32)+4;
  x4=j5+6;
  xm=3;
  fc=-4;
  n33=0;

  while (x4>=1) {
      xm = xm + fc;
      fc += n33;
      n33 += 6;
      x4 = x4/2;
  }

}
