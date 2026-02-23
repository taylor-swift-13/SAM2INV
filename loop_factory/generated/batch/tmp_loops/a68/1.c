int main1(int m,int q){
  int k, u, v, c;

  k=q;
  u=0;
  v=-5;
  c=m;

  while (u<=k-3) {
      v = v*2+4;
      c = c*v+4;
      v = v+c;
  }

}
