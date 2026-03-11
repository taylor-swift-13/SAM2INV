int main1(){
  int nj, k3, czd, zx5, j1;

  nj=20;
  k3=0;
  czd=0;
  zx5=0;
  j1=nj;

  while (zx5<nj) {
      zx5++;
      czd = czd + 1;
      j1 = j1 + zx5;
  }

  while (nj<k3) {
      j1 += 1;
      nj = nj + 1;
      j1 = j1 + czd;
  }

}
