int main1(int j,int f){
  int kt, g2d, u9, z, sv, nl, m, x7;

  kt=32;
  g2d=0;
  u9=5;
  z=1;
  sv=-1;
  nl=f;
  m=0;
  x7=0;

  while (1) {
      if (!(g2d+6<=kt)) {
          break;
      }
      if (sv==kt+1) {
          u9 = u9 + 3;
          z = z + 3;
      }
      else {
          u9 += 2;
          z += 2;
      }
      if (!(!(sv==kt))) {
          u9 = u9 + 1;
          sv += 1;
      }
      nl = nl+z-u9;
      x7 = x7 + 3;
      m = m + sv;
      j = j+u9-u9;
      kt = (g2d+6)-1;
  }

}
