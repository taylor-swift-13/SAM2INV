int main1(int d){
  int u1m, tl5z, bh, exi, p4g, s4, j, c8, nt;
  u1m=72;
  tl5z=0;
  bh=d;
  exi=0;
  p4g=-8;
  s4=d;
  j=tl5z;
  c8=0;
  nt=tl5z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant exi == (tl5z % 2);
  loop invariant s4 + bh == 2 * \at(d, Pre) + tl5z;
  loop invariant s4 - bh == (tl5z % 2);
  loop invariant s4 == \at(d,Pre) + ((tl5z + 1) / 2);
  loop invariant 0 <= tl5z <= u1m;
  loop invariant bh == \at(d,Pre) + (tl5z / 2);
  loop assigns bh, c8, d, exi, j, nt, p4g, s4, tl5z;
*/
while (tl5z < u1m) {
      if (!(exi!=0)) {
          s4 += 1;
          j += d;
      }
      else {
          bh++;
          p4g += d;
      }
      tl5z = tl5z + 1;
      exi = tl5z % 2;
      if (c8+3<u1m) {
          c8 += nt;
      }
      d += j;
      nt = nt+(tl5z%2);
      nt += d;
      d = d + c8;
      nt = nt + c8;
  }
}