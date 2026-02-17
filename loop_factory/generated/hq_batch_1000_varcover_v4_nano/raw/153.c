int main1(int k,int n,int p){
  int l, i, v, t, b, f;

  l=30;
  i=l;
  v=6;
  t=l;
  b=3;
  f=p;

  while (i>0) {
      v = v+5;
      b = b+1;
      if ((i%7)==0) {
          b = b+1;
      }
      else {
          b = b+4;
      }
      i = i-1;
  }

}
