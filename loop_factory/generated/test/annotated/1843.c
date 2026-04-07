int main1(){
  int yts, or, rpt, dw, fy3;
  yts=1;
  or=0;
  rpt=0;
  dw=0;
  fy3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rpt == or * or;
  loop invariant rpt == fy3*fy3;
  loop invariant ((fy3 % 3) == 0) ==> (dw == 3*(fy3/3));
  loop invariant 0 <= or;
  loop invariant or <= yts;
  loop invariant 0 <= fy3;
  loop assigns rpt, fy3, or, dw;
*/
while (or < yts) {
      rpt = rpt + 2*or + 1;
      fy3++;
      or = or + 1;
      dw = dw+(fy3%3);
  }
}