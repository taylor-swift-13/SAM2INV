int main1(int m,int n){
  int l, i, v, g;

  l=72;
  i=l;
  v=m;
  g=1;

  while (i>0) {
      g = g+g;
      g = g+v;
      i = i-1;
  }

  while (l<i) {
      l = l+4;
  }

}
