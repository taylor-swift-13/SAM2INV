int main1(int b,int q){
  int n, u, v, h;

  n=38;
  u=0;
  v=q;
  h=q;

  while (u<n) {
      h = v;
      v = v+2;
      v = v+h+h;
  }

}
