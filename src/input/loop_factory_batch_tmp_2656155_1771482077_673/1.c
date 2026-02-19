int main1(int a,int n){
  int l, i, v;

  l=n+24;
  i=0;
  v=0;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v<l) {
      i = i-i;
      v = v+1;
  }

}
