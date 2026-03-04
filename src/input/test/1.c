int main1(int a,int m,int p){
  int n, v, f;

  n=m-1;
  v=0;
  f=1;

  while (1) {
      if (f==1) {
          f = 2;
      }
      else {
          if (f==2) {
              f = 1;
          }
      }
      if (v+5<=m+n) {
          f = f+v;
      }
      f = f*f+f;
      if ((v%6)==0) {
          f = f*f;
      }
      f = f%6;
  }

}
