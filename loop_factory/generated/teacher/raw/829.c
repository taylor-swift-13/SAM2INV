int main1(int k,int n,int p){
  int e, t, f, d, v, w;

  e=(n%8)+16;
  t=0;
  f=0;
  d=1;
  v=6;
  w=0;

  while (w<=e) {
      w = w+1;
      f = f+d;
      d = d+v;
      v = v+2;
  }

}
