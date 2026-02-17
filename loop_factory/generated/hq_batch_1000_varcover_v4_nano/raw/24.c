int main1(int b,int n,int q){
  int l, i, v;

  l=62;
  i=0;
  v=i;

  while (i<l) {
      v = v+v;
      if (v+4<l) {
          v = v*i;
      }
      i = i+1;
  }

}
