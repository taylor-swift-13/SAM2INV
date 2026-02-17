int main1(int b,int m,int n,int p){
  int l, i, v, x, d, c;

  l=(m%35)+20;
  i=0;
  v=p;
  x=p;
  d=b;
  c=b;

  while (i<l) {
      v = v+4;
      x = x+v;
      d = d+x;
      if (d+5<l) {
          v = v+1;
      }
      i = i+1;
  }

}
