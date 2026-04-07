int main1(){
  int v4, j9, ba0, h9p, fz, yy, r1k6, rq;
  v4=45;
  j9=0;
  ba0=8;
  h9p=16;
  fz=0;
  yy=5;
  r1k6=j9;
  rq=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j9 <= v4;
  loop invariant fz == 0;
  loop invariant ba0 + j9 == 8;
  loop invariant yy >= 5;
  loop invariant rq >= 2;
  loop invariant r1k6 >= 0;
  loop invariant yy <= 5 + j9;
  loop invariant (h9p - j9) == 16;
  loop assigns ba0, h9p, fz, j9, rq, yy, r1k6;
*/
while (1) {
      if (!(j9<v4)) {
          break;
      }
      if (!(fz!=0)) {
          ba0--;
          h9p = h9p + 1;
          fz = 0;
      }
      else {
          ba0 = ba0 + 1;
          h9p--;
          fz = 1;
      }
      j9++;
      if (rq+3<v4) {
          rq += yy;
      }
      yy = yy+(j9%2);
      r1k6 = r1k6 + rq;
      rq += yy;
  }
}