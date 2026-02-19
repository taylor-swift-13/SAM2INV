int main1(int k,int q){
  int l, i, v, p;

  l=k;
  i=0;
  v=q;
  p=l;

  while (i<l) {
      v = v*2;
      p = p/2;
      v = v+1;
  }

  while (i<l) {
      v = v+1;
      p = p+v;
      i = i+1;
  }

}
