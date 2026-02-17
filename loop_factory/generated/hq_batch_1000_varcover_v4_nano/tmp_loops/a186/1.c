int main1(int a,int b,int p,int q){
  int l, i, v, r, w, s, h;

  l=p;
  i=0;
  v=q;
  r=q;
  w=q;
  s=i;
  h=p;

  while (i<l) {
      v = v*2;
      r = r+v;
      w = w%6;
      if (i+2<=p+l) {
          v = v*v+h;
      }
      r = r%7;
      if (w*w<=l+5) {
          h = h*v;
      }
      i = i+1;
  }

}
