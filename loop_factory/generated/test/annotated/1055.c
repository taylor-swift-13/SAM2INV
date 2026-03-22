int main1(){
  int m7o, qpx, p8n, eo, nb, fk;
  m7o=(1%40)+6;
  qpx=m7o;
  p8n=0;
  eo=-2;
  nb=m7o;
  fk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eo == p8n - 2;
  loop invariant nb == m7o + p8n*(m7o - 2) + p8n*(p8n + 1)/2;
  loop invariant eo <= m7o;
  loop invariant nb == 7 + 5*p8n + p8n*(p8n + 1)/2;
  loop assigns p8n, eo, nb;
*/
while (eo<=m7o-1) {
      p8n += 1;
      eo += 1;
      nb += eo;
      nb = nb + qpx;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m7o - qpx == 0;
  loop invariant nb - eo == ((p8n*p8n) + 9*p8n + 18) / 2;
  loop invariant fk == qpx * (eo - m7o);
  loop invariant nb - eo == 90;
  loop assigns eo, nb, p8n, fk;
*/
while (eo<m7o) {
      eo += 1;
      nb++;
      p8n = (p8n+m7o)+(-(qpx));
      fk = fk + qpx;
  }
}