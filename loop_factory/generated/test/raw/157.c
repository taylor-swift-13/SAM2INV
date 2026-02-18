int main1(int m,int n,int p,int q){
  int l, i, v;

  l=p-6;
  i=0;
  v=1;

  while (i<l) {
      if (v+1<l) {
          v = v+v;
      }
      i = i+1;
  }

}
