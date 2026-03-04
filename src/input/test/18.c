int main18(int a,int m,int n){
  int f, j, u, w;

  f=m;
  j=0;
  u=0;
  w=(a%28)+10;

  while (w>u) {
      w = w-u;
      u = u+1;
      w = w+w;
      w = w+u;
      u = u+1;
  }

}
