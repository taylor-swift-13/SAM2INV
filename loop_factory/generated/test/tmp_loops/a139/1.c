int main1(int m,int n){
  int l, i, v, r;

  l=n-10;
  i=0;
  v=l;
  r=n;

  while (i<l) {
      v = v+1;
      i = i+1;
  }

  while (r<l) {
      i = i+1;
      v = v+1;
      i = i+3;
  }

}
