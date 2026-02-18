int main1(int a,int b,int m,int n){
  int l, i, v, g, x;

  l=30;
  i=l;
  v=l;
  g=6;
  x=l;

  while (i>0) {
      v = v+3;
      x = x+2;
      if (i+5<=v+l) {
          x = g-x;
      }
      v = v+3;
      i = i-1;
  }

}
