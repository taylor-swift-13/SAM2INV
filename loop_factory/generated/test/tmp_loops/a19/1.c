int main1(int a,int k){
  int l, i, v, t;

  l=52;
  i=0;
  v=l;
  t=i;

  while (i<l) {
      v = v+1;
      t = t+v;
      i = i+1;
  }

  while (l<v) {
      t = t+1;
      l = l+5;
  }

}
