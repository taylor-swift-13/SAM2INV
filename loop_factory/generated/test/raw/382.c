int main1(int j){
  int s5k, kh, ebol, pj, k;

  s5k=19;
  kh=0;
  ebol=-2;
  pj=s5k;
  k=kh;

  while (1) {
      if (!(ebol<s5k)) {
          break;
      }
      pj = s5k-ebol;
      k += pj;
      ebol++;
  }

}
