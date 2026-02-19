int main1(int b,int k){
  int l, i, v, d;

  l=b;
  i=0;
  v=i;
  d=-2;

  while (i<l) {
      v = v+1;
      d = d+1;
      d = d+d;
  }

  while (d>0) {
      l = l+l;
      l = l+1;
      d = d-1;
  }

}
