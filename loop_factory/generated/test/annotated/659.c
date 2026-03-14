int main1(int w){
  int xss, z, w5, ca;
  xss=w;
  z=4;
  w5=0;
  ca=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w5 == ca * w;
  loop invariant ca >= 0;
  loop assigns w5, ca;
*/
while (1) {
      if (!(ca<xss)) {
          break;
      }
      w5 = w5 + w;
      ca++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ca >= 0;
  loop invariant 2*xss == 2*w + ca * ((z-4)*(z-4) + 7*(z-4));
  loop invariant 4 <= z;
  loop assigns xss, z;
*/
while (1) {
      if (!(z-1>=0)) {
          break;
      }
      xss = xss+ca*z;
      z += 1;
  }
}