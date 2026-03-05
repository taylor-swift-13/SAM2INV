int main194(int o){
  int wzji, ny, t208, is, b0, d6t6;

  wzji=o+12;
  ny=0;
  t208=-1;
  is=wzji;
  b0=-8;
  d6t6=ny;

  while (ny<=wzji-1) {
      is = is/2;
      t208 = t208*2;
      b0 = b0*is;
      if (d6t6+3<wzji) {
          d6t6 = d6t6*b0;
      }
      else {
          o = o%4;
      }
      ny = ny + 1;
  }

}
