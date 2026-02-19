int main1(int a,int b){
  int l, i, v, p;

  l=b;
  i=l;
  v=i;
  p=8;

  while (i>0) {
      v = v+p+p;
      v = v+1;
      i = i-1;
  }

  while (v<p) {
      l = l+v;
      v = v+2;
  }

}
