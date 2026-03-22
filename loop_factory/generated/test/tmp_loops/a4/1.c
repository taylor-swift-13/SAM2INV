int main1(){
  int o, v, f5, g9, yx, cjj, fo;

  o=55;
  v=1;
  f5=1;
  g9=1;
  yx=1;
  cjj=-2;
  fo=12;

  while (1) {
      if (!(g9<=o)) {
          break;
      }
      v = v*(1/g9);
      if ((g9/2)%2==0) {
          yx = 1;
      }
      else {
          yx = -1;
      }
      f5 = f5+yx*v;
      g9++;
      v = v*(1/g9);
      if (o*o<=o+4) {
          fo = fo*fo+cjj;
      }
      cjj = cjj+(v%9);
      cjj = cjj + fo;
  }

}
