int main1(int b,int k){
  int l, i, v, g;

  l=b+8;
  i=l;
  v=b;
  g=4;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (g<i) {
      v = v+2;
      v = v+v;
      g = g*2;
  }

}
