int main114(int a,int n,int q){
  int d, j, v, e, c;

  d=n+7;
  j=0;
  v=-4;
  e=0;
  c=n;

  while (1) {
      v = v*3+3;
      e = e*v+3;
  }

  while (d>=1) {
      if (e+3<=c) {
          e = e+3;
      }
      else {
          e = c;
      }
  }

}
