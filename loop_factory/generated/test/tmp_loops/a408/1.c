int main1(int k,int q){
  int l, i, v, t;

  l=(k%12)+12;
  i=0;
  v=l;
  t=-5;

  while (i<l) {
      v = v+t+t;
      v = v+1;
      i = i+1;
  }

  while (t<i) {
      v = v+1;
      t = t+1;
  }

}
