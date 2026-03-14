int main1(){
  int lz, c, x, xn, bl;
  lz=1+15;
  c=0;
  x=0;
  xn=-6;
  bl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*bl == x*(x+1);
  loop invariant (0 <= x);
  loop invariant (x <= lz);
  loop invariant (xn <= lz - x);
  loop assigns x, xn, bl;
*/
while (1) {
      if (!(x<lz)) {
          break;
      }
      x = x + 1;
      xn = lz-x;
      bl += x;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bl == 136 + c*(c-1)/2;
  loop invariant 0 <= c;
  loop invariant c <= lz;
  loop invariant bl == (lz*(lz+1))/2 + c*(c-1)/2;
  loop assigns bl, c, xn;
*/
while (1) {
      if (!(c<lz)) {
          break;
      }
      bl = bl + c;
      c = c + 1;
      xn = xn + c;
  }
}