int main1(int d){
  int k, i, s, nf01;

  k=59;
  i=0;
  s=i;
  nf01=-6;

  while (1) {
      if (!(i < k)) {
          break;
      }
      s = s + d*(1 - 2*(i >= k/2));
      nf01 = nf01 + k;
      i = k;
  }

}
