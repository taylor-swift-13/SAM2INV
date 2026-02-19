int main1(int k,int q){
  int l, i, v, c;

  l=q+6;
  i=l;
  v=-2;
  c=l;

  while (i>0) {
      v = v+c+c;
      i = i-1;
  }

  while (c>0) {
      v = v+v;
      c = c-1;
  }

}
