int main19(int p,int c,int q){
  int zt, b9, an, b1, c8, c4cs;

  zt=p;
  b9=zt;
  an=5;
  b1=5;
  c8=9;
  c4cs=0;

  while (an>0&&b1>0&&c8>0) {
      if (b9%3==0) {
          an--;
      }
      if (b9%3==1) {
          b1--;
      }
      if (b9%3==2) {
          c8 = c8 - 1;
      }
      c4cs = c4cs + an;
      b9 += 1;
      c4cs = c4cs*2;
  }

}
