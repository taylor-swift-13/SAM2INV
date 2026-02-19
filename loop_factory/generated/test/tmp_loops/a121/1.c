int main1(int b,int p){
  int l, i, v, g;

  l=(p%22)+20;
  i=0;
  v=l;
  g=l;

  while (i<l) {
      v = v+4;
      g = g+4;
      i = i+1;
  }

  while (i>0) {
      g = g+2;
      l = l+4;
      i = i-1;
  }

}
