int main1(){
  int jw, ws, d8, n, sb, o2r, dj;
  jw=0;
  ws=-3;
  d8=8;
  n=0;
  sb=jw;
  o2r=jw;
  dj=1+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jw == 0;
  loop invariant ws <= 0;
  loop invariant o2r == 0;
  loop invariant dj == 3;
  loop invariant sb == 0;
  loop invariant n == 0;
  loop invariant d8 == 8;
  loop assigns d8, n, sb, ws, o2r, dj;
*/
while (ws!=d8) {
      if (!(ws<=d8)) {
          d8 -= ws;
          n = n + sb;
      }
      else {
          ws -= d8;
          sb += n;
      }
      o2r = o2r + sb;
      dj = dj+(sb%8);
  }
}