int main1(int a,int b,int m,int q){
  int l, i, v, n, z;

  l=(a%23)+16;
  i=0;
  v=b;
  n=i;
  z=q;

  while (i<l) {
      v = v*v+v;
      v = v%9;
      n = n*z;
      i = i+1;
  }

}
