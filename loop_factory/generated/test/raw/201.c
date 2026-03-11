int main1(){
  int hqwg, s, p1, kq, al;

  hqwg=1+24;
  s=hqwg;
  p1=-3;
  kq=0;
  al=hqwg;

  while (1) {
      if (!(p1<=hqwg)) {
          break;
      }
      kq = kq+p1*p1;
      p1 += 1;
      al = al + p1;
  }

  while (p1<al) {
      s = al-p1;
      hqwg += kq;
      p1 += 1;
  }

}
