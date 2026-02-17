int main1(int a,int b,int m,int p){
  int l, i, v, r, t;

  l=27;
  i=l;
  v=l;
  r=l;
  t=i;

  while (i>0) {
      v = v+1;
      r = r+v;
      t = t+5;
      if (t<a+5) {
          t = r-t;
      }
      r = r+i;
      r = r+1;
      i = i-1;
  }

}
