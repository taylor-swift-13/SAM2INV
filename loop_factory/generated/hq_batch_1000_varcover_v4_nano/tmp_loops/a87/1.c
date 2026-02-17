int main1(int a,int b,int k,int n){
  int l, i, v, e, w, t, d;

  l=k+6;
  i=0;
  v=n;
  e=1;
  w=2;
  t=-1;
  d=k;

  while (i<l) {
      v = v+e;
      e = e+w;
      w = w+3;
      e = e*e+v;
      if (w+4<l) {
          v = d*d;
      }
      if ((i%5)==0) {
          e = e*e+w;
      }
      else {
          t = w*w;
      }
      i = i+1;
  }

}
