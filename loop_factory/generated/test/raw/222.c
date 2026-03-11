int main1(){
  int j, wt9n, yl3, b, z, a0u;

  j=25;
  wt9n=0;
  yl3=0;
  b=0;
  z=j;
  a0u=0;

  while (1) {
      if (!(b<j)) {
          break;
      }
      yl3++;
      b += 1;
      z += wt9n;
      a0u = a0u+(yl3%9);
  }

  while (1) {
      if (!(z<=wt9n-1)) {
          break;
      }
      z += 1;
      yl3 += wt9n;
      a0u++;
  }

}
