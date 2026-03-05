int main1(int j,int y){
  int r, jlsk, xzt, vv2;

  r=80;
  jlsk=3;
  xzt=0;
  vv2=9;

  while (jlsk<r) {
      if (xzt==0) {
          xzt += 2;
          vv2 -= 2;
          xzt = 1;
      }
      else {
          xzt -= 2;
          vv2 += 2;
          xzt = 0;
      }
      jlsk++;
      j += xzt;
  }

}
