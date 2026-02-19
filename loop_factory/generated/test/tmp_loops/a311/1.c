int main1(int a,int b){
  int l, i, v, k;

  l=36;
  i=0;
  v=b;
  k=-4;

  while (i<l) {
      k = k+k;
      k = k+v;
      i = i+4;
  }

  while (k<l) {
      v = v+i+i;
      k = k+1;
  }

}
