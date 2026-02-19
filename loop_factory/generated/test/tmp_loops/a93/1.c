int main1(int n,int q){
  int l, i, v, p;

  l=q+8;
  i=0;
  v=l;
  p=-1;

  while (i<l) {
      v = v+2;
      p = p+v;
      i = i+1;
  }

  while (p<v) {
      p = p+1;
  }

}
