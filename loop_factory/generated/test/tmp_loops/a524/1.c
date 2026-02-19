int main1(int n,int p){
  int l, i, v, t;

  l=n+7;
  i=l;
  v=p;
  t=4;

  while (i>0) {
      v = v+5;
      i = i-1;
  }

  while (v<i) {
      t = t+1;
      v = v+1;
  }

}
