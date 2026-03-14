int main1(){
  int vx, n, u4, a, u;

  vx=1;
  n=3;
  u4=1;
  a=0;
  u=n;

  while (1) {
      if (!(u4<=vx-1)) {
          break;
      }
      u += vx;
      a++;
      u4 = 2*u4;
      u = u + 1;
  }

}
