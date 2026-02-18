int main1(int k,int m,int n,int p){
  int l, i, v;

  l=k+11;
  i=0;
  v=k;

  while (i<l) {
      v = v+v;
      v = v+1;
      if ((i%2)==0) {
          v = v+2;
      }
      i = i+1;
  }

}
