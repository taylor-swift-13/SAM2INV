int main1(int p,int q){
  int c, x, l;

  c=p+10;
  x=0;
  l=-5;

  while (x<c) {
      l = l+3;
      if (x<l+3) {
          l = l-l;
      }
  }

}
