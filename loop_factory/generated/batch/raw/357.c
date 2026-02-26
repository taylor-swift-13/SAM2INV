int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=r;
  v=t;

  while (t<=r-1) {
      e = e+1;
      v = v-1;
      v = v+3;
      t = t+1;
  }

}
