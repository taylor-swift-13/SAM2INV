int main1(){
  int y, j, bl, tz, fc, c1u;
  y=56;
  j=0;
  bl=1;
  tz=6;
  fc=0;
  c1u=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tz == 6 + 2*fc;
  loop invariant c1u == j + bl;
  loop invariant 0 <= fc;
  loop invariant fc <= y + 1;
  loop invariant bl == fc*fc + 5*fc + 1;
  loop invariant j == fc*(fc*fc + 6*fc - 4)/3;
  loop assigns fc, j, bl, tz, c1u;
*/
while (fc<=y) {
      fc = fc + 1;
      j += bl;
      bl += tz;
      tz += 2;
      c1u += bl;
  }
}