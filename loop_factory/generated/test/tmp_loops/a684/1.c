int main1(int a,int n){
  int l, i, v, r;

  l=71;
  i=0;
  v=a;
  r=i;

  while (i<l) {
      v = v+5;
      r = r+v;
      i = i+1;
  }

  while (v<r) {
      v = v+4;
  }

}
