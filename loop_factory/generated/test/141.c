int main141(int a,int b,int n){
  int f, k, o, u;

  f=a;
  k=2;
  o=b;
  u=b;

  while (1) {
      if (k>=f) {
          break;
      }
      o = o+3;
      k = k+1;
      o = o+1;
      u = u-1;
      if ((k%2)==0) {
          u = u+o;
      }
  }

}
