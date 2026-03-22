int main1(){
  int p, l, q, hq, ot, bs, mna, vtp, h, ymze;

  p=1;
  l=-5;
  q=p;
  hq=0;
  ot=p;
  bs=p;
  mna=p;
  vtp=-6;
  h=6;
  ymze=p;

  while (1) {
      if (!(l+1<=p)) {
          break;
      }
      if (!(!(l<p/2))) {
          q += 1;
      }
      else {
          q = q + hq;
      }
      if (l+6<=vtp+p) {
          ot += 1;
      }
      h = h + q;
      ymze = ymze+(l%2);
      bs = bs + q;
      mna = mna + q;
      hq++;
      ot = ot + hq;
      p = (l+1)-1;
      if (ymze+6<p) {
          ot += 1;
      }
  }

}
