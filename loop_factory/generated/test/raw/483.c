int main1(int u){
  int fq, gt, pwn, t, cvh, wnr;

  fq=0;
  gt=0;
  pwn=(u%28)+10;
  t=fq;
  cvh=u;
  wnr=u;

  while (pwn>gt) {
      pwn = pwn - gt;
      u = (fq)+(u);
      cvh = cvh + 3;
      wnr = wnr + 3;
      gt = gt + 1;
  }

  while (t>pwn) {
      t = t - pwn;
      u = u + cvh;
      pwn += 1;
      if (fq*fq<=cvh+5) {
          u = u%4;
      }
  }

}
