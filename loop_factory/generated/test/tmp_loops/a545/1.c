int main1(int n,int p){
  int l, i, v, w;

  l=n-8;
  i=l;
  v=2;
  w=p;

  while (i>0) {
      v = v+1;
      w = w+v;
      i = i-1;
  }

  while (w<i) {
      l = l*4;
      v = v/4;
  }

}
