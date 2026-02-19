int main1(int m,int p){
  int l, i, v, e;

  l=m;
  i=1;
  v=p;
  e=p;

  while (i<l) {
      v = v+1;
      e = e-1;
      v = v+e+e;
  }

  while (l<v) {
      i = i+l;
      l = l+1;
  }

}
