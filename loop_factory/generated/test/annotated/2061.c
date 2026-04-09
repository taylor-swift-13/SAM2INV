int main1(){
  int gl, y0, ix8y, v, zyx, e;
  gl=1+25;
  y0=gl+3;
  ix8y=y0;
  v=gl;
  zyx=3;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zyx - 6*e == 3;
  loop invariant v == 26 + 3*e*e;
  loop invariant ix8y == 29 + 26*e + (e*(e-1)*(2*e-1))/2;
  loop invariant 0 <= e;
  loop invariant e <= gl + 1;
  loop invariant v == gl + 3*e*e;
  loop invariant ix8y == (gl + 3) + e*gl + (e*(e-1)*(2*e-1))/2;
  loop assigns ix8y, v, e, zyx;
*/
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