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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j, Pre);
  loop invariant g2d == 0;
  loop invariant kt >= g2d + 5;
  loop invariant nl <= \at(f, Pre);
  loop invariant m <= 0;
  loop invariant x7 >= 0;
  loop invariant (kt == 32 || kt == 5);
  loop invariant (sv == -1);
  loop invariant u9 >= 5;
  loop invariant f == \at(f, Pre);
  loop invariant u9 - z == 4;
  loop assigns j, kt, u9, z, sv, nl, x7, m;
*/
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