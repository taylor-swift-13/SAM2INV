int main1(int a,int b){
  int l, i, v, g;

  l=(a%29)+10;
  i=l;
  v=a;
  g=l;

  while (i>0) {
      i = i/2;
  }

  while (i<v) {
      l = l+1;
      g = g-1;
  }

}
