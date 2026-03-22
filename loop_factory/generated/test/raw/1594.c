int main1(){
  int ytd, kpi, c0u, d47, rc4, en, n7h, lk, ou;

  ytd=78;
  kpi=0;
  c0u=22;
  d47=0;
  rc4=1;
  en=0;
  n7h=ytd;
  lk=ytd;
  ou=25;

  while (1) {
      if (!(c0u>0&&kpi<ytd)) {
          break;
      }
      if (c0u<rc4) {
          en = c0u;
      }
      else {
          en = rc4;
      }
      d47 = d47 + en;
      c0u = c0u - en;
      if (kpi%2==0) {
          rc4 += 2;
      }
      else {
          rc4++;
      }
      kpi = kpi + 1;
      n7h += 1;
      lk = lk+ytd-kpi;
      ou += c0u;
  }

}
