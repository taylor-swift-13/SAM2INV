int main180(int m,int d){
  int ur, fa8, ti3, nh3, whw0, rp;

  ur=d+12;
  fa8=ur;
  ti3=d;
  nh3=ur;
  whw0=fa8;
  rp=(d%6)+2;

  while (1) {
      if (whw0>=ur) {
          break;
      }
      ti3 = ti3*rp+d;
      nh3 = nh3*rp;
      whw0 = whw0 + 1;
      rp = rp*4+(ti3%7)+2;
      d += ti3;
  }

}
