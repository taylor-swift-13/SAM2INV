int main1(int q){
  int iia, e9, v7gz, zbjt, gcv;

  iia=q+11;
  e9=iia;
  v7gz=0;
  zbjt=1;
  gcv=0;

  while (1) {
      if (!(e9<iia)) {
          break;
      }
      gcv += 1;
      zbjt++;
      if (zbjt>=3) {
          zbjt = zbjt - 3;
          v7gz += 1;
      }
      e9 += 1;
  }

}
