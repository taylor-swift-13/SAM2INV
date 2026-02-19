int main1(int b,int q){
  int l, i, v, k;

  l=q-6;
  i=0;
  v=-2;
  k=l;

  while (i<l) {
      v = v*2;
      k = k/2;
      v = v+k+k;
  }

  while (l>0) {
      i = i+i;
      i = i+l;
      l = l-1;
  }

}
