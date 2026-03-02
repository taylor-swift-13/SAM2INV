int main1(int m,int n){
  int g, i, c;

  g=(n%17)+17;
  i=0;
  c=g;

  while (1) {
      c = c+c;
      if (c+2<g) {
          c = c+1;
      }
      i = i+1;
  }

}
