int main1(int b,int q){
  int l, d, k;

  l=32;
  d=0;
  k=q;

  while (d<l) {
      k = k+3;
      if (k+7<l) {
          k = k+2;
      }
      k = k+k;
  }

}
