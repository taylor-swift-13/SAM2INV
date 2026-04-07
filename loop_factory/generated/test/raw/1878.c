int main1(int o){
  int tn4p, s, lks, va, d9, se, b94, guq, c;

  tn4p=o*5;
  s=6;
  lks=s;
  va=1;
  d9=tn4p;
  se=o;
  b94=tn4p;
  guq=o;
  c=0;

  while (s<tn4p) {
      if (d9==tn4p+1) {
          lks = lks + 3;
          va = va + 3;
      }
      else {
          lks += 2;
          va += 2;
      }
      if (d9==tn4p) {
          lks = lks + 1;
          d9++;
      }
      c = c+lks-va;
      guq = guq+d9-lks;
      se = se + b94;
      o += 2;
      s = tn4p;
      if (!(!((s%2)==0))) {
          guq += 2;
      }
  }

}
