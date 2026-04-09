int main1(int j){
  int k, krf, pb2;

  k=(j%10)+14;
  krf=0;
  pb2=j;

  while (j-- > 0) {
      pb2 += pb2;
      krf = (krf + 1 > k) ? (2*k - (krf + 1)) : ((krf - 1 < 0) ? -(krf - 1) : (krf + 1));
      j++;
  }

}
