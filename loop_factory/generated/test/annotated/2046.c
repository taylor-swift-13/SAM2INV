int main1(){
  int w, td4, rmt, xr, qfq;
  w=29;
  td4=0;
  rmt=1;
  xr=0;
  qfq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant td4 <= w;
  loop invariant xr == (td4 * w);
  loop invariant (td4 == 0 && rmt == 1) || (td4 >= 1 && rmt == 0);
  loop invariant qfq == 0;
  loop assigns rmt, qfq, xr, td4;
*/
while (1) {
      if (!(td4 < w)) {
          break;
      }
      rmt = rmt * xr;
      qfq = qfq + rmt;
      xr = xr + w;
      td4++;
  }
}