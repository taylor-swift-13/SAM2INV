int main1(int k,int m,int n,int p){
  int l, i, v, o, w;

  l=18;
  i=0;
  v=l;
  o=k;
  w=k;

  while (i<l) {
      o = o+w;
      w = w+v;
      w = o-w;
      if (v<o+3) {
          v = v+1;
      }
      o = o-l;
      i = i+2;
  }

}
