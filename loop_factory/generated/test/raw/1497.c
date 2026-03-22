int main1(){
  int kc, bi, gw1, sfn, kx, x63;

  kc=(1%26)+4;
  bi=0;
  gw1=1;
  sfn=1;
  kx=0;
  x63=1;

  while (bi < kc) {
      kx += 1;
      bi += 1;
      sfn = sfn + bi;
      gw1 = x63 * sfn * (kx + 1);
  }

}
