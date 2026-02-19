int main1(int m,int q){
  int l, i, v, t;

  l=(m%16)+18;
  i=0;
  v=1;
  t=l;

  while (i<l) {
      v = v+1;
      t = t-1;
  }

  while (v>0) {
      l = l-l;
      v = v/2;
  }

}
