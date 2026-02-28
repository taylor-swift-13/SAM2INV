int main159(int a,int m,int q){
  int u, c, p;

  u=67;
  c=u;
  p=0;

  while (c>1) {
      p = p+2;
      p = p-m;
  }

  while (p<=u-1) {
      c = c*2;
      c = c%6;
      if (c+7<u) {
          c = c*c;
      }
      c = c%3;
      p = p+1;
  }

  while (u<c) {
      p = p*p;
      p = p%9;
      u = u+5;
  }

}
