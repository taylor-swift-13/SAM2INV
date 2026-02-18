int main1(int b,int k,int m,int q){
  int l, i, v, g;

  l=31;
  i=l;
  v=q;
  g=k;

  while (i>0) {
      v = v+g;
      g = g+g;
      g = g+3;
      i = i-1;
  }

}
