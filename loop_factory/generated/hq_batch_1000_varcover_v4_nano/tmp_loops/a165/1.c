int main1(int b,int k,int n,int q){
  int l, i, v, o, f, p;

  l=79;
  i=l;
  v=q;
  o=q;
  f=q;
  p=b;

  while (i>0) {
      v = v*3;
      o = o/3;
      v = v*2;
      o = o+v;
      f = f%2;
      f = f*2;
      if ((i%6)==0) {
          p = p%7;
      }
  }

}
