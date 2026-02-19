int main1(int b,int p){
  int l, i, v, g;

  l=b;
  i=0;
  v=b;
  g=i;

  while (i<l) {
      v = v+1;
      g = g+v;
      i = i+1;
  }

  while (v<i) {
      g = g+1;
      l = l-1;
      v = v+1;
  }

}
