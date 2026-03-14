int main1(){
  int v5j5, qfm, qet, s, v0, ch;

  v5j5=1*4;
  qfm=0;
  qet=-4;
  s=qfm;
  v0=qfm;
  ch=v5j5;

  while (qet+1<=v5j5) {
      s = qet;
      ch += qfm;
      qet = qet + 1;
  }

  while (1) {
      if (!(qet<v5j5)) {
          break;
      }
      v0++;
      qet = qet + 1;
      if ((s%4)==0) {
          v0 += v0;
      }
  }

}
