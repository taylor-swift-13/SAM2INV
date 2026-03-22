int main1(int n,int u){
  int ce, ny, y, dmt, zz9;

  ce=53;
  ny=ce;
  y=0;
  dmt=n;
  zz9=(n%35)+8;

  while (1) {
      if (!(zz9>0)) {
          break;
      }
      ny = ny+y*y;
      dmt = dmt+zz9*zz9;
      y = y+zz9*zz9;
      n += ce;
      zz9 -= 1;
  }

}
