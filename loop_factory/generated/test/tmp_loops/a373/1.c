int main1(int k,int n){
  int l, i, v;

  l=n;
  i=0;
  v=k;

  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+3;
  }

  while (v<l) {
      v = v+1;
  }

}
