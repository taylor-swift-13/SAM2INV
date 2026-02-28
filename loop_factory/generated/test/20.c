int main20(int n,int p,int q){
  int m, l, a, v, u;

  m=71;
  l=0;
  a=(q%6)+2;
  v=l;
  u=0;

  while (u<m) {
      u = u+1;
      a = a*a+1;
      v = v*a;
      a = a*a+a;
      a = a%9;
  }

  while (1) {
      v = v*2;
      a = a+v;
      m = m%3;
      u = u+1;
  }


  /*@ assert \false; */
}
