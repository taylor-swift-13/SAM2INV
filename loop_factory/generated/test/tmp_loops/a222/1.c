int main1(int n,int q){
  int l, i, v;

  l=55;
  i=0;
  v=4;

  while (i<l) {
      v = v+i;
      v = l%9;
      i = i+2;
  }

  while (l>0) {
      i = i-i;
      l = l-1;
  }

}
