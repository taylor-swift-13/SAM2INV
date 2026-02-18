int main1(int k,int m,int p,int q){
  int l, i, v, e, y;

  l=70;
  i=0;
  v=5;
  e=2;
  y=m;

  while (i<l) {
      v = v+1;
      e = e+v;
      if (k<q+5) {
          y = y+i;
      }
      else {
          v = v+5;
      }
      v = v+1;
      i = i+1;
  }

}
