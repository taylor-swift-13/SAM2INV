int main1(int p,int q){
  int l, i, v, f;

  l=q+15;
  i=0;
  v=-4;
  f=3;

  while (i<l) {
      f = f+f;
      f = f+v;
      i = i+1;
  }

  while (l<i) {
      l = l+1;
  }

}
