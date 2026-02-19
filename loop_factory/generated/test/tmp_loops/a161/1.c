int main1(int a,int b){
  int l, i, v, t;

  l=(b%35)+20;
  i=1;
  v=l;
  t=l;

  while (i<l) {
      v = v+1;
      t = t-1;
      v = v+1;
  }

  while (i<v) {
      t = t+1;
      i = i+1;
  }

}
