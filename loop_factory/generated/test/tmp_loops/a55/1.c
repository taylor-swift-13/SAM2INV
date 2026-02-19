int main1(int a,int n){
  int l, i, v;

  l=n;
  i=0;
  v=-4;

  while (i<l) {
      v = v+i;
      i = i+2;
  }

  while (l>0) {
      v = v+1;
      l = l-1;
  }

}
