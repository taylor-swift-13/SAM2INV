int main1(int a,int q){
  int l, i, v, g;

  l=23;
  i=0;
  v=3;
  g=i;

  while (i<l) {
      v = v*2;
      g = g/2;
  }

  while (v<l) {
      i = i+g+g;
      i = i+1;
      v = v+1;
  }

}
