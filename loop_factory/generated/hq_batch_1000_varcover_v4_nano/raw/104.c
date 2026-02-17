int main1(int b,int n,int p){
  int l, i, v, x;

  l=63;
  i=l;
  v=p;
  x=n;

  while (i>0) {
      v = v+x+x;
      v = v+1;
      v = x-v;
      i = i-1;
  }

}
