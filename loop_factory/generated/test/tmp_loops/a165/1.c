int main1(int b,int n){
  int l, i, v, t;

  l=b+23;
  i=0;
  v=l;
  t=i;

  while (i<l) {
      v = v*2;
      t = t/2;
      t = t+t;
  }

  while (i>0) {
      t = t+v+v;
      i = i-1;
  }

}
