int main1(int n,int p){
  int l, i, v, a;

  l=n-4;
  i=0;
  v=i;
  a=p;

  while (i<l) {
      v = v*4;
      a = a/4;
      v = v+a+a;
  }

  while (a>0) {
      i = i-i;
      i = i+a;
      a = a-1;
  }

}
