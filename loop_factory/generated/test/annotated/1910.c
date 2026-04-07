int main1(int b){
  int oq, r6, ocv, sx, x2, wcl, eb, xs, bw, uk;
  oq=b-1;
  r6=0;
  ocv=b;
  sx=2;
  x2=0;
  wcl=0;
  eb=b*2;
  xs=r6;
  bw=1;
  uk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oq == \at(b,Pre) - 1;
  loop invariant sx == 2 + ((r6 + 1) / 2);
  loop invariant r6 >= 0;
  loop invariant uk == 2 * r6;
  loop invariant ocv == \at(b, Pre) + r6/2;
  loop invariant 0 <= xs;
  loop invariant 0 <= x2;
  loop assigns r6, ocv, sx, xs, wcl, b, uk, x2, eb, bw;
*/
while (1) {
      if (!(r6 < oq)) {
          break;
      }
      r6 = r6 + 1;
      if (((r6 % 2) == 0)) {
          ocv++;
      }
      else {
          sx++;
      }
      if (xs+2<oq) {
          xs += uk;
      }
      wcl += ocv;
      b = b + sx;
      uk += 2;
      x2 = x2 + sx;
      x2 += 4;
      eb += 2;
      eb = b-eb;
      bw = bw + eb;
  }
}