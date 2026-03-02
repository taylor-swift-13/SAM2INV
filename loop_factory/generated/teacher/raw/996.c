int main1(int a,int b){
  int m, n, l, v;

  m=(b%40)+13;
  n=0;
  l=0;
  v=n;

  while (l<m) {
      if (l>=m/2) {
          v = v+4;
      }
      l = l+1;
      v = v+v;
  }

}
