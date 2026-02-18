int main1(int m,int n,int p,int q){
  int l, i, v;

  l=57;
  i=l;
  v=l;

  while (i>0) {
      v = v*2;
      if (v+1<l) {
          v = v*v;
      }
      v = v%9;
      i = i-1;
  }

}
