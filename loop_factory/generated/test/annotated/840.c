int main1(){
  int d5kq, q65, dqcr, rypl, i6p;
  d5kq=28;
  q65=0;
  dqcr=-2;
  rypl=6;
  i6p=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d5kq == 28;
  loop invariant 6 <= rypl;
  loop invariant rypl <= d5kq;
  loop invariant i6p > 0;
  loop invariant q65 >= 0;
  loop invariant dqcr <= -2;
  loop assigns q65, dqcr, rypl, i6p;
*/
while (1) {
      if (rypl>=d5kq) {
          break;
      }
      q65 = q65*i6p+1;
      dqcr = dqcr*i6p;
      rypl += 1;
      i6p = i6p*4+(rypl%7)+2;
  }
}