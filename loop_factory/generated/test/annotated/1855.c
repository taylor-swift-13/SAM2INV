int main1(int r,int y){
  int g, gvr, zr, h, m, yo, zp;
  g=(y%9)+8;
  gvr=0;
  zr=0;
  h=0;
  m=0;
  yo=0;
  zp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == (y % 9) + 8;
  loop invariant gvr == zp;
  loop invariant zr >= 0;
  loop invariant h >= 0;
  loop invariant m >= 0;
  loop invariant yo >= 0;
  loop invariant r == \at(r,Pre) + gvr*(gvr + 1);
  loop invariant zr + h + m + yo == gvr;
  loop invariant gvr >= 0;
  loop assigns gvr, zr, h, m, yo, zp, r;
*/
while (gvr<g+(y%7)) {
      if (gvr%11==0) {
          zr += 1;
      }
      else {
          if (gvr%5==0) {
              h += 1;
          }
          else {
              if (gvr%3==0) {
                  m++;
              }
              else {
                  if (1) {
                      yo++;
                  }
              }
          }
      }
      gvr += 1;
      zp = zp + 1;
      r = r + gvr;
      r += zp;
  }
}