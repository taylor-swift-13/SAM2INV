int main1(){
  int io, vi, lm, kzi, w, i, sjh, ei, h, sp;
  io=133;
  vi=0;
  lm=vi;
  kzi=2;
  w=vi;
  i=8;
  sjh=io;
  ei=io;
  h=-5;
  sp=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == vi + 8;
  loop invariant ei == 133;
  loop invariant w == 0;
  loop invariant h == -5 || h == 3;
  loop invariant lm == 2*vi;
  loop invariant kzi == 2*vi + 2;
  loop invariant (0 <= vi <= io);
  loop invariant sjh == 133 + 8*vi + vi*(vi + 1)/2;
  loop assigns lm, kzi, w, i, ei, h, sjh, vi;
*/
while (1) {
      if (w==io+1) {
          lm = lm + 3;
          kzi = kzi + 3;
      }
      else {
          lm += 2;
          kzi += 2;
      }
      if (!(!(w==io))) {
          lm++;
          w += 1;
      }
      i = i + 1;
      ei = ei + w;
      h = h+w-w;
      sjh = sjh + i;
      if ((vi%2)==0) {
          h = sp-h;
      }
      vi++;
      if (vi>=io) {
          break;
      }
  }
}