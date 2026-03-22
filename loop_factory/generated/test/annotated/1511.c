int main1(){
  int qo, iy, s, jdf, d, ek, l, asvc, yy, w4, orl;
  qo=1;
  iy=1;
  s=0;
  jdf=0;
  d=0;
  ek=0;
  l=0;
  asvc=0;
  yy=0;
  w4=iy;
  orl=qo;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant asvc == jdf + 2*d + 3*ek + 4*l;
  loop invariant 0 <= yy <= 4*s;
  loop invariant 0 <= s;
  loop invariant jdf + d + ek + l == s;
  loop invariant s <= qo;
  loop invariant 0 <= d;
  loop invariant 0 <= ek;
  loop invariant 0 <= l;
  loop invariant 0 <= orl;
  loop invariant orl < 3;
  loop invariant 0 <= w4;
  loop invariant w4 < 9;
  loop invariant 0 <= jdf;
  loop invariant 0 <= yy <= 4;
  loop assigns s, jdf, d, ek, l, asvc, orl, yy, w4;
*/
while (1) {
      if (!(s<qo)) {
          break;
      }
      if (s%7==0) {
          jdf += 1;
          asvc = asvc + 1;
      }
      else {
          if (s%6==0) {
              d++;
              asvc += 2;
          }
          else {
              if (s%5==0) {
                  ek++;
                  asvc = asvc + 3;
              }
              else {
                  if (1) {
                      l = l + 1;
                      asvc += 4;
                  }
              }
          }
      }
      s++;
      orl = (orl+jdf)%3;
      yy = yy+s%5;
      w4 = (w4+ek)%9;
  }
}