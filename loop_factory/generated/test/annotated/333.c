int main1(){
  int hib, yh, wj, yl, jn, mc;
  hib=1;
  yh=0;
  wj=0;
  yl=0;
  jn=6;
  mc=hib;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wj == yl;
  loop invariant jn == 6 + 2 * yl;
  loop invariant ((yl % 3) == 1) ==> (mc % 3 == 2);
  loop invariant ((yl % 3) != 1) ==> (mc % 3 == 1);
  loop invariant mc >= 1;
  loop invariant ((yl % 3) == 0) ==> (mc == 1 + 3*(yl/3));
  loop invariant 0 <= yl;
  loop invariant yl <= hib;
  loop assigns wj, jn, yl, mc;
*/
while (yl<hib) {
      wj = wj + 1;
      jn += 2;
      yl++;
      mc = mc+(wj%3);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yl;
  loop invariant 0 <= yh;
  loop assigns yh, yl;
*/
while (yl>0) {
      if (yl%2==0) {
          yh = yh + hib;
      }
      else {
          yh = yh+hib+1;
      }
      yl = 0;
  }
}