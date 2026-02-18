int main1(int a,int n){
  int l, i, v;

  l=n-2;
  i=0;
  v=a;

  while (i<l) {
      v = v*v+v;
      v = v+v;
      i = i+1;
  }

}
