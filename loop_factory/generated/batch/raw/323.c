int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=r;
  v=t;

  while (t<=r-1) {
      e = e+3;
      v = v+2;
      if (t<e+5) {
          v = v+1;
      }
      else {
          v = v+r;
      }
      t = t+1;
  }

}
