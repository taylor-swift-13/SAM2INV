int main1(int b,int n){
  int l, i, v, r;

  l=8;
  i=l;
  v=b;
  r=b;

  while (i>0) {
      v = v+1;
      r = r+v;
      i = i-1;
  }

  while (r<l) {
      i = i*2;
      v = v/2;
      i = i+3;
  }

}
