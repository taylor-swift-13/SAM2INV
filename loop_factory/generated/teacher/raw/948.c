int main1(int n,int p){
  int h, i, l;

  h=(n%18)+10;
  i=0;
  l=n;

  while (1) {
      l = l+3;
      l = l-l;
      if ((i%4)==0) {
          l = l+1;
      }
  }

}
