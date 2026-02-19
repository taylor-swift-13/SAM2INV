int main1(int p,int q){
  int l, i, v, a;

  l=(p%12)+15;
  i=0;
  v=i;
  a=l;

  while (i<l) {
      v = v+a+a;
      i = i+1;
  }

  while (i<v) {
      i = i+5;
  }

}
