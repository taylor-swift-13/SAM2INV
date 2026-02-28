int main193(int k,int n,int q){
  int y, o, t, h;

  y=n+18;
  o=1;
  t=5;
  h=k;

  while (o*2<=y) {
      t = t+o;
      h = h*h;
      h = h+t*h;
      o = o*2;
  }

}
