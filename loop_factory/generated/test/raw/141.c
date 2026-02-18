int main1(int b,int m,int n,int p){
  int l, i, v, g;

  l=80;
  i=0;
  v=b;
  g=-3;

  while (i<l) {
      v = v+g+g;
      v = v+1;
      g = n-5;
      v = v+g;
      if (g+1<l) {
          g = g+v;
      }
      i = i+1;
  }

}
