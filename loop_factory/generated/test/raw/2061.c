int main1(){
  int gl, y0, ix8y, v, zyx, e;

  gl=1+25;
  y0=gl+3;
  ix8y=y0;
  v=gl;
  zyx=3;
  e=0;

  while (1) {
      if (e>gl) {
          break;
      }
      ix8y += v;
      v = (zyx)+(v);
      e += 1;
      zyx += 6;
  }

}
