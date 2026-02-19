int main1(int a,int n){
  int l, i, v;

  l=28;
  i=0;
  v=n;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v<l) {
      i = i+5;
      v = v*2;
  }

}
