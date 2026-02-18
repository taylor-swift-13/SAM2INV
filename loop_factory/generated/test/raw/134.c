int main1(int k,int m,int n,int p){
  int l, i, v, u;

  l=9;
  i=l;
  v=8;
  u=-5;

  while (i>0) {
      v = v+1;
      u = u-1;
      v = v+1;
      v = v+i;
      if ((i%9)==0) {
          u = u+4;
      }
      else {
          v = u-v;
      }
      if (i+2<=i+l) {
          v = m+i;
      }
      i = i-1;
  }

}
