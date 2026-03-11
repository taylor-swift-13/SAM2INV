int main1(int m){
  int et, p9w, hts, qb, xq2;
  et=(m%15)+20;
  p9w=0;
  hts=1;
  qb=5;
  xq2=p9w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant et == \at(m, Pre) % 15 + 20;
  loop invariant 1 <= hts;
  loop invariant hts <= et + 1;
  loop invariant qb == 5 + (hts - 1) * hts * (2 * hts - 1) / 6;
  loop assigns qb, hts, m;
*/
while (1) {
      if (!(hts<=et)) {
          break;
      }
      qb = qb+hts*hts;
      hts += 1;
      m = m + hts;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant et == \at(m, Pre) % 15 + 20;
  loop invariant 0 <= xq2;
  loop invariant xq2 <= et;
  loop invariant 0 <= p9w;
  loop invariant (xq2 == 0 ==> p9w == 0) &&
                   (xq2 > 0  ==> p9w == (et - (xq2 - 1)));
  loop invariant (xq2 == 0) ==> p9w == 0;
  loop invariant (xq2 > 0) ==> p9w == et - xq2 + 1;
  loop assigns p9w, xq2, m;
*/
while (xq2<et) {
      p9w = et-xq2;
      xq2++;
      m = m + xq2;
  }
}