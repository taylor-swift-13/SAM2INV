int main1(int k,int n,int p,int q){
  int l, i, v, a, w;

  l=(n%11)+6;
  i=0;
  v=p;
  a=l;
  w=p;

  while (i<l) {
      v = v*3;
      a = a/3;
      v = v+1;
      a = a-1;
      w = w+1;
      w = w+v;
      if (w+7<l) {
          w = a-w;
      }
  }

}
