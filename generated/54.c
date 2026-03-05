int main54(int e){
  int tm, owf, zr, c, of, mm5u;

  tm=e*2;
  owf=3;
  zr=19;
  c=0;
  of=1;
  mm5u=0;

  while (1) {
      if (!(zr>0&&owf<tm)) {
          break;
      }
      if (zr<of) {
          mm5u = zr;
      }
      else {
          mm5u = of;
      }
      zr -= mm5u;
      owf += 1;
      c += mm5u;
      of = of + 1;
  }

}
