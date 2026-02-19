int main1(int n,int p){
  int l, i, v, r;

  l=n+12;
  i=0;
  v=-2;
  r=l;

  while (i<l) {
      v = v*3;
      r = r/3;
  }

  while (r>0) {
      l = l+1;
      l = l+4;
      r = r-1;
  }

}
