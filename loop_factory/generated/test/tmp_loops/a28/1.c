int main1(){
  int l, u6, kgk, r6u, n, kb, ae, t4;

  l=79;
  u6=0;
  kgk=0;
  r6u=0;
  n=0;
  kb=u6;
  ae=u6;
  t4=0;

  while (u6<l) {
      r6u = r6u + 1;
      n += 1;
      if (r6u>=8) {
          r6u -= 8;
          kgk += 1;
      }
      u6 = u6 + 1;
      if (kb+3<l) {
          kb = kb*2;
      }
      kb = kb + u6;
      ae = ae + u6;
      ae = ae*ae;
      t4 = t4+kb*ae;
      ae = ae + kb;
  }

}
