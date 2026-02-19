int main1(int a,int n){
  int l, i, v, x;

  l=a;
  i=0;
  v=i;
  x=a;

  while (i<l) {
      v = v+1;
      x = x-1;
      x = x+x;
  }

  while (l>0) {
      x = x+1;
      v = v+x;
      l = l/2;
  }

}
