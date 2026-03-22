int main1(){
  int iiy, fsy, ka, t, b6v, g;

  iiy=1+14;
  fsy=0;
  ka=fsy;
  t=-3;
  b6v=1;
  g=0;

  while (ka<=iiy) {
      t = t*ka;
      if (ka<iiy) {
          b6v = b6v*ka;
      }
      g = g*2+(b6v%4)+2;
      ka = ka + 1;
  }

}
