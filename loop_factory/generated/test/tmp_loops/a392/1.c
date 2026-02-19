int main1(int p,int q){
  int l, i, v;

  l=q+8;
  i=1;
  v=q;

  while (i<l) {
      i = i*2;
  }

  while (i>0) {
      l = l+1;
      l = l+l;
      i = i-1;
  }

}
