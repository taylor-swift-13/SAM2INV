int main1(int a,int q){
  int l, k, u, v, x;

  l=q+11;
  k=1;
  u=8;
  v=l;
  x=4;

  while (1) {
      if (x<=v) {
          v = x;
      }
      u = u+1;
      v = v-1;
      x = x+1;
      if (u<k+3) {
          v = v-3;
      }
  }

}
