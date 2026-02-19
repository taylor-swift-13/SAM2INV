int main1(int a,int n){
  int l, i, v, k;

  l=n+8;
  i=l;
  v=l;
  k=-6;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (i>0) {
      v = v+k+k;
      v = v+1;
      i = i-1;
  }

}
