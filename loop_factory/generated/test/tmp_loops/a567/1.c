int main1(int a,int q){
  int l, i, v, x;

  l=(q%32)+16;
  i=0;
  v=6;
  x=i;

  while (i<l) {
      v = v+x+x;
      i = i+1;
  }

  while (v<l) {
      i = i*4;
      x = x/4;
      i = i+5;
  }

}
