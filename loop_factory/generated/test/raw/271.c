int main1(int k){
  int bz, nj, npah;

  bz=63;
  nj=bz;
  npah=-1;

  while (nj>0) {
      if (nj<bz/2) {
          npah = npah + npah;
      }
      else {
          npah = npah + 1;
      }
      k = k+(nj%2);
      k = bz+k;
  }

}
