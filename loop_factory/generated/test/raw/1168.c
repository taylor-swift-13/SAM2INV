int main1(){
  int hq, qzp, gi, en, x;

  hq=1-10;
  qzp=0;
  gi=1;
  en=1;
  x=0;

  while (gi<=hq) {
      qzp += 1;
      en += 2;
      x = x + qzp;
      gi = gi + en;
  }

}
