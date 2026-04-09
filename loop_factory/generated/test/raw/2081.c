int main1(){
  int d2cm, aa, dh, frn;

  d2cm=1+13;
  aa=0;
  dh=1;
  frn=d2cm;

  while (1) {
      if (!(aa < d2cm && dh <= frn)) {
          break;
      }
      aa += 1;
      frn -= dh;
      dh += 2;
  }

}
