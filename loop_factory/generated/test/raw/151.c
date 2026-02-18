int main1(int a,int b,int m,int q){
  int l, i, v, d;

  l=q;
  i=0;
  v=-2;
  d=0;

  while (i<l) {
      d = d+d;
      d = d+v;
      v = v+2;
      v = v+d;
      i = i+1;
  }

}
