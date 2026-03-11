int main1(int m){
  int et, p9w, hts, qb, xq2;

  et=(m%15)+20;
  p9w=0;
  hts=1;
  qb=5;
  xq2=p9w;

  while (1) {
      if (!(hts<=et)) {
          break;
      }
      qb = qb+hts*hts;
      hts += 1;
      m = m + hts;
  }

  while (xq2<et) {
      p9w = et-xq2;
      xq2++;
      m = m + xq2;
  }

}
