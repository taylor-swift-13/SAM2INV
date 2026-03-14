int main1(int c,int o){
  int l, zr, xk, z1, r1z;

  l=12;
  zr=0;
  xk=0;
  z1=0;
  r1z=12;

  while (1) {
      if (!(z1<l)) {
          break;
      }
      r1z += zr;
      z1 = z1 + 1;
      xk = xk + c;
  }

  while (xk<=z1-1) {
      xk += 1;
      zr = zr + c;
      l += zr;
  }

}
