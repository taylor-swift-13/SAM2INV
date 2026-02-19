int main1(int p,int q){
  int l, i, v;

  l=(p%31)+6;
  i=0;
  v=l;

  while (i<l) {
      v = v+v;
      i = i+5;
  }

  while (l<i) {
      l = l+1;
  }

}
