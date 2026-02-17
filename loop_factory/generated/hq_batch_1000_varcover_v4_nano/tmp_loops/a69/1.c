int main1(int m,int n,int p,int q){
  int l, i, v, o, h, w, k, g, s;

  l=m-2;
  i=l;
  v=0;
  o=p;
  h=q;
  w=6;
  k=p;
  g=-8;
  s=m;

  while (i>0) {
      v = v+o;
      o = o+h;
      h = h+3;
      k = k%8;
      if (o+2<l) {
          w = w*w+v;
      }
      i = i/2;
  }

}
