int main1(int i,int x){
  int ku, z3, kt;

  ku=34;
  z3=0;
  kt=1;

  while (z3<ku) {
      if (kt>=12) {
          kt = -1;
      }
      if (kt<=2) {
          kt = 1;
      }
      kt = kt + kt;
      z3 += 1;
      i = i + kt;
  }

}
