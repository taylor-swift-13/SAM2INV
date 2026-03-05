int main1(){
  int xssf, yx, lctw;
  xssf=1+8;
  yx=0;
  lctw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yx;
  loop invariant yx <= xssf;
  loop invariant xssf == 9;
  loop invariant (lctw == 0) ==> (yx == 0);
  loop invariant 0 <= lctw <= 3;
  loop assigns lctw, yx;
*/
while (yx<xssf) {
      lctw++;
      if (lctw>=4) {
          lctw -= 4;
          lctw++;
      }
      yx++;
  }
}