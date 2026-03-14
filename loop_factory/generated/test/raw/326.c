int main1(int m){
  int kv, d02, jq, nb, rh, c9lc;

  kv=100;
  d02=0;
  jq=1;
  nb=-3;
  rh=0;
  c9lc=0;

  while (nb<kv) {
      rh = rh + 3;
      nb++;
      jq = jq + m;
      c9lc += nb;
  }

  while (rh<=jq-1) {
      c9lc = c9lc + m;
      kv += d02;
      rh += 1;
      kv = kv + m;
  }

}
