int main1(int a,int n,int p,int q){
  int l, i, v, u;

  l=p;
  i=0;
  v=6;
  u=4;

  while (i<l) {
      if (i<l/2) {
          v = v+u;
      }
      else {
          v = v+1;
      }
      v = v+1;
      u = u-1;
  }

}
