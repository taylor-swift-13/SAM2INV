int main1(int i){
  int dgp, zfq5, zgt, x4;

  dgp=20;
  zfq5=0;
  zgt=i;
  x4=dgp;

  while (zfq5 < i && zfq5 < dgp) {
      zfq5 = zfq5 + (dgp / (zfq5 + 1));
      x4 = x4 + zgt;
      zgt += 1;
  }

}
