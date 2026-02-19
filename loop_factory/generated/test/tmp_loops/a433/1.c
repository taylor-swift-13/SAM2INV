int main1(int b,int q){
  int l, i, v, k;

  l=9;
  i=l;
  v=-3;
  k=q;

  while (i>0) {
      k = k+k;
      k = k+v;
      i = i-1;
  }

  while (k<v) {
      k = k+1;
  }

}
