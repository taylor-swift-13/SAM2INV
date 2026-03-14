int main1(int u){
  int fq, gt, pwn, t, cvh, wnr;
  fq=0;
  gt=0;
  pwn=(u%28)+10;
  t=fq;
  cvh=u;
  wnr=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pwn == (((\at(u,Pre) % 28) + 10) - ((gt * (gt - 1)) / 2));
  loop invariant cvh == (\at(u,Pre)) + 3*gt;
  loop invariant wnr == (\at(u,Pre)) + 3*gt;
  loop invariant u == \at(u,Pre) + fq;
  loop invariant gt >= 0;
  loop invariant u == \at(u, Pre);
  loop assigns pwn, u, cvh, wnr, gt;
*/
while (pwn>gt) {
      pwn = pwn - gt;
      u = (fq)+(u);
      cvh = cvh + 3;
      wnr = wnr + 3;
      gt = gt + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= 0;
  loop invariant fq == 0;
  loop assigns t, pwn, u;
*/
while (t>pwn) {
      t = t - pwn;
      u = u + cvh;
      pwn += 1;
      if (fq*fq<=cvh+5) {
          u = u%4;
      }
  }
}