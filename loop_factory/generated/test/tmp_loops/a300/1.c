int main1(int b,int n){
  int l, i, v;

  l=49;
  i=0;
  v=b;

  while (i<l) {
      v = l*b;
      i = i+4;
  }

  while (v<l) {
      i = i+i;
      i = i+n;
      v = v+1;
  }

}
