int main1(){
  int s5, z, ktb, v5, sx;

  s5=1;
  z=(1%28)+8;
  ktb=(1%22)+5;
  v5=0;
  sx=0;

  while (ktb!=0) {
      if (ktb%2==1) {
          v5 += z;
          ktb--;
      }
      ktb = ktb/2;
      z = 2*z;
      sx = sx*2+(z%2)+2;
      sx += s5;
  }

}
