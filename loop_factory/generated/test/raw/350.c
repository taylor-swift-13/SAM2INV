int main1(){
  int ky, t9, qlh, pse, qw;

  ky=1-7;
  t9=ky;
  qlh=(1%18)+5;
  pse=(1%15)+3;
  qw=qlh;

  while (qlh!=0) {
      pse -= 1;
      qlh -= 1;
      qw = qw+ky-t9;
  }

  while (pse<ky) {
      pse++;
      qw++;
      qlh += qw;
  }

}
