int main1(int a,int q){
  int r, t, v, n;

  r=q;
  t=0;
  v=t;
  n=r;

  while (v!=0&&n!=0) {
      if (v>n) {
          v = v-n;
      }
      else {
          n = n-v;
      }
  }

}
