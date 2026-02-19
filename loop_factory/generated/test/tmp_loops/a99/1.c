int main1(int n,int p){
  int l, i, v, d;

  l=p+6;
  i=l;
  v=8;
  d=p;

  while (i>0) {
      d = d+d;
      i = i-1;
  }

  while (i<d) {
      v = v+3;
      l = l+v;
      i = i+3;
  }

}
