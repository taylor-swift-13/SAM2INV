int main1(int m,int n,int p,int q){
  int l, i, v, o;

  l=79;
  i=l;
  v=q;
  o=3;

  while (i>0) {
      v = v+1;
      o = o+v;
      o = 1;
      v = o-v;
      v = v+1;
      o = o+i;
      i = i-1;
  }

}
