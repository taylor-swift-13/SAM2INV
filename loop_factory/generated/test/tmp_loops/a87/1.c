int main1(int a,int p){
  int l, i, v, t;

  l=(a%24)+8;
  i=0;
  v=p;
  t=8;

  while (i<l) {
      v = v+1;
      i = i+2;
  }

  while (t<v) {
      l = l+1;
      i = i-1;
  }

}
