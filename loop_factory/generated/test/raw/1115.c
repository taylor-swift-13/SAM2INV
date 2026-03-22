int main1(int r){
  int g9, ic, j, z, u;

  g9=r+14;
  ic=0;
  j=0;
  z=r+4;
  u=g9;

  while (1) {
      if (!(j<=g9-1)) {
          break;
      }
      j++;
      ic += r;
      z += j;
  }

  while (u*2<=ic) {
      j = j+g9*u;
      ic = (u*2)-1;
  }

}
