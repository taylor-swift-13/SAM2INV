int main1(int y){
  int u, xcq, xkm, q0, b1, n;

  u=43;
  xcq=1;
  xkm=xcq;
  q0=xcq;
  b1=u;
  n=13;

  while (xcq*4<=u) {
      q0 += 1;
      xkm = xkm+q0*q0;
      b1 = b1*2+(xkm%6)+2;
      n = n*3+(xkm%2)+1;
      u = (xcq*4)-1;
  }

}
