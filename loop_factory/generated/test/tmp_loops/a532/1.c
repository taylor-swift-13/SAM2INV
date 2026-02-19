int main1(int k,int n){
  int l, i, v, g;

  l=(k%12)+15;
  i=0;
  v=l;
  g=k;

  while (i<l) {
      i = i+1;
  }

  while (g<i) {
      v = v*5;
      v = v+v;
      g = g+1;
  }

}
