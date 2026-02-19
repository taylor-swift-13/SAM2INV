int main1(int a,int m){
  int l, i, v;

  l=40;
  i=0;
  v=a;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (v<i) {
      l = l+v;
      v = v+1;
  }

}
