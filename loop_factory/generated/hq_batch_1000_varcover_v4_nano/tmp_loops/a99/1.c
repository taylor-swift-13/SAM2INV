int main1(int a,int k,int n,int p){
  int l, i, v, w, q, o, e, g;

  l=39;
  i=l;
  v=3;
  w=p;
  q=i;
  o=i;
  e=l;
  g=-1;

  while (i>0) {
      v = v*2;
      w = w+v;
      q = q%7;
      v = v*v+w;
      q = q*o;
      i = i/2;
  }

}
