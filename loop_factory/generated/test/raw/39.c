int main1(int a,int b,int k,int m){
  int l, i, v, g;

  l=(k%14)+18;
  i=0;
  v=l;
  g=m;

  while (i<l) {
      v = v+1;
      g = g+v;
      v = v+6;
      i = i+1;
  }

}
