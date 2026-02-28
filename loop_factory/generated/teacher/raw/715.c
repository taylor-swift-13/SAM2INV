int main1(int a,int b,int k,int p){
  int r, h, u, f, j, x, v, e;

  r=a-5;
  h=0;
  u=p;
  f=r;
  j=0;
  x=2;
  v=h;
  e=k;

  while (1) {
      x = x*x+u;
      u = u%5;
      f = f*j;
      x = x*f;
      x = x*2;
      e = u*u;
      h = h+1;
  }

}
