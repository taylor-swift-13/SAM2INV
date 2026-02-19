int main1(int n,int p){
  int l, i, v, b;

  l=p;
  i=0;
  v=l;
  b=p;

  while (i<l) {
      v = v+1;
      b = b+v;
      i = i+1;
  }

  while (l<b) {
      v = v+v;
      l = l+1;
  }

}
