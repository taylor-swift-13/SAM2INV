int main1(int h){
  int zb, ld, iwf, rp, qtr, nbk;
  zb=h-7;
  ld=0;
  iwf=43;
  rp=0;
  qtr=1;
  nbk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iwf + rp == 43;
  loop invariant 0 <= ld;
  loop invariant qtr == ld + 1;
  loop invariant 0 <= rp <= 43;
  loop invariant zb == \at(h, Pre) - 7;
  loop assigns nbk, qtr, ld, iwf, rp;
*/
while (1) {
      if (!(iwf>0&&ld<zb)) {
          break;
      }
      if (iwf<=qtr) {
          nbk = iwf;
      }
      else {
          nbk = qtr;
      }
      qtr++;
      ld++;
      iwf = iwf - nbk;
      rp = rp + nbk;
  }
}