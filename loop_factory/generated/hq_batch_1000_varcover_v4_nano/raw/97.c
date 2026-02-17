int main1(int b,int k,int p){
  int l, i, v, h, o, q, z, c;

  l=60;
  i=l;
  v=p;
  h=p;
  o=0;
  q=0;
  z=l;
  c=k;

  while (i>0) {
      v = v*2;
      h = h+v;
      o = o%2;
      z = o*o;
      o = o%8;
      i = i-1;
  }

}
