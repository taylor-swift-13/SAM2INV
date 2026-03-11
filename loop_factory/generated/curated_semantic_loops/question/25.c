int main1(int m){
  int et, p9w, hts, qb, xq2;
  et=(m%15)+20;
  p9w=0;
  hts=1;
  qb=5;
  xq2=p9w;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (hts<=et) {
      qb = qb+hts*hts;
      hts += 1;
      m = m + hts;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */

while (xq2<et) {
      p9w = et-xq2;
      xq2++;
      m = m + xq2;
  }
/*@
  assert !(xq2<et) &&
         (et == \at(m, Pre) % 15 + 20);
*/

}