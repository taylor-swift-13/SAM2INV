int main1(int a,int b,int k,int n){
  int l, i, v, r, g;

  l=15;
  i=0;
  v=a;
  r=i;
  g=a;

  while (i<l) {
      v = v+1;
      r = r-1;
      v = g-v;
      r = r+3;
      r = r+g;
      i = i+1;
  }

}
