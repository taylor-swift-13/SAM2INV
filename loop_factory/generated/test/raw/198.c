int main1(int v){
  int ip, dje, qzk, gf, am1;

  ip=(v%23)+6;
  dje=0;
  qzk=0;
  gf=0;
  am1=0;

  while (qzk<ip) {
      gf += qzk;
      am1 = am1 + gf;
      qzk = qzk + 1;
  }

  while (gf<dje) {
      am1 = dje-gf;
      gf += 8;
      ip = ip + gf;
  }

}
