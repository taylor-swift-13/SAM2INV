int main1(int m,int n,int p,int q){
  int l, i, v;

  l=(p%7)+12;
  i=0;
  v=l;

  while (i<l) {
      if ((i%4)==0) {
          v = v+v;
      }
      i = i+1;
  }

}
