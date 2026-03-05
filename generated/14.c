int main14(int o,int w,int p){
  int kt6z, yd, krh, nz2, mvl5, f8;

  kt6z=o;
  yd=p;
  krh=o;
  nz2=0;
  mvl5=(o%6)+2;
  f8=o;

  while (1) {
      if (nz2>=kt6z) {
          break;
      }
      krh = krh*mvl5;
      yd = yd*mvl5+o;
      nz2 = nz2 + 1;
      mvl5 = mvl5+(yd%6);
      f8 = f8 + yd;
  }

}
