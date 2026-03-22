int main1(){
  int vs98, w5, v, eb6, f, xc, j, z, jn;
  vs98=1+6;
  w5=vs98;
  v=vs98;
  eb6=w5;
  f=0;
  xc=vs98;
  j=w5;
  z=vs98;
  jn=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eb6 == v;
  loop invariant w5 == xc;
  loop invariant z == w5;
  loop invariant jn == 10;
  loop invariant f == 0;
  loop invariant 2 * j == w5 * w5 + w5 - 42;
  loop invariant v - 2*w5 == -7;
  loop invariant w5 >= 7;
  loop invariant vs98 == 7;
  loop assigns v, eb6, w5, xc, z, j, f, jn;
*/
while (1) {
      if (!(w5-1>=0)) {
          break;
      }
      if (f==vs98+1) {
          v = v + 3;
          eb6 = eb6 + 3;
      }
      else {
          v += 2;
          eb6 += 2;
      }
      if (f==vs98) {
          v++;
          f = f + 1;
      }
      xc = xc + 1;
      jn = jn+eb6-eb6;
      z += 1;
      j = j + xc;
      w5++;
  }
}