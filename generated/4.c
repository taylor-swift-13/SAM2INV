int main4(int e,int n){
  int raf, rgd, p, md, a;

  raf=15;
  rgd=raf;
  p=-8723;
  md=6;
  a=n;

  while (1) {
      if (!(p<=-5)) {
          break;
      }
      p = p+md-2;
      a = a + 3;
      e = e+raf-rgd;
      md += 1;
      e = e*e+a;
      a = a%6;
  }

}
