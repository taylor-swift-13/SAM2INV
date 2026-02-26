int main1(int p,int q){
  int r, k, l, s;

  r=(p%6)+4;
  k=r;
  l=6;
  s=8;

  while (k-1>=0) {
      if (l+3<=r) {
          l = l+3;
      }
      else {
          l = r;
      }
      l = l+s;
  }

}
