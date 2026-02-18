int main1(int m,int n){
  int l, i, v;

  l=n;
  i=0;
  v=m;

  while (i<l) {
      v = v%4;
      v = v*v;
      i = i+1;
  }

}
