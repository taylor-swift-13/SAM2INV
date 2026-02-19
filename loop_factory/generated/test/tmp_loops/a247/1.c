int main1(int b,int q){
  int l, i, v, y;

  l=(q%10)+18;
  i=0;
  v=l;
  y=q;

  while (i<l) {
      v = v+3;
      i = i+1;
  }

  while (i<v) {
      y = y+1;
      l = l+1;
      y = y+5;
  }

}
