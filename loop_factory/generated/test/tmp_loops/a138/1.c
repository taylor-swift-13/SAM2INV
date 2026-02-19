int main1(int a,int b){
  int l, i, v, u;

  l=a;
  i=l;
  v=b;
  u=a;

  while (i>0) {
      v = v+u+u;
      i = i/2;
  }

  while (l<i) {
      l = l+1;
  }

}
