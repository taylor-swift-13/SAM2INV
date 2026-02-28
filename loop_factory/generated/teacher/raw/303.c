int main1(int p,int q){
  int u, t, v;

  u=62;
  t=0;
  v=p;

  while (t<=u-1) {
      if (v+3<u) {
          v = v+v;
      }
      v = v+1;
      v = v+t;
      t = t+1;
  }

}
