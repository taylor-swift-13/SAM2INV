int main1(){
  int cp, wh, j5, lyr, f6, sq, c, uc, pt, gcp;
  cp=1+15;
  wh=0;
  j5=2;
  lyr=wh;
  f6=cp;
  sq=20;
  c=wh;
  uc=cp;
  pt=cp;
  gcp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gcp == ((wh + 3) / 4);
  loop invariant pt == cp + ((wh + 2) / 4);
  loop invariant uc == cp + ((wh + 1) / 4);
  loop invariant lyr == wh / 4;
  loop invariant 0 <= wh <= cp;
  loop invariant pt - 16 == (wh + 2) / 4;
  loop invariant uc - 16 == (wh + 1) / 4;
  loop invariant 0 <= c <= 3;
  loop invariant f6 >= 16;
  loop invariant j5 >= 2;
  loop invariant sq >= 20;
  loop invariant gcp + pt + uc + lyr == wh + 32;
  loop assigns c, gcp, pt, uc, lyr, f6, j5, wh, sq;
*/
while (wh < cp) {
      c = wh % 4;
      if (c == 0) {
          gcp += 1;
      }
      else {
      }
      if (c == 1) {
          pt = pt + 1;
      }
      else {
      }
      if (c == 2) {
          uc = uc + 1;
      }
      else {
      }
      if (c == 3) {
          lyr++;
      }
      else {
      }
      f6 += pt;
      j5 += uc;
      wh++;
      f6 += sq;
      sq = sq + j5;
      j5 = (f6)+(j5);
      j5 += sq;
  }
}