int main1(int b,int k,int p){
  int l, i, v, x, t, g;

  l=(k%7)+12;
  i=0;
  v=k;
  x=p;
  t=2;
  g=p;

  while (i<l) {
      v = v+x;
      x = x+t;
      i = i+1;
  }

}
