int main1(){
  int hev, b, xv;
  hev=1*3;
  b=1;
  xv=hev;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hev == 3;
  loop invariant 1 <= b;
  loop invariant b <= hev;
  loop invariant xv - hev == (b - 1) * b / 2;
  loop assigns xv, b;
*/
while (1) {
      xv += b;
      if (xv+4<hev) {
          xv += b;
      }
      b += 1;
      if (b>=hev) {
          break;
      }
  }
}