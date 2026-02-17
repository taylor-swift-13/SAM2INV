int main1(int a,int m,int n,int q){
  int l, i, v, c, e, x;

  l=66;
  i=l;
  v=n;
  c=l;
  e=n;
  x=n;

  while (i>0) {
      v = v+1;
      c = c-1;
      v = v+x;
      if (i+5<=c+l) {
          v = v+1;
      }
      else {
          v = v+e;
      }
      v = v+i;
      e = e+c;
      i = i-1;
  }

}
