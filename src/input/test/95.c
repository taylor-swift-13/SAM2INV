int main95(int m,int n,int p){
  int k, i, v;

  k=p+10;
  i=k;
  v=2;

  while (i>=1) {
      if (v==1) {
          v = 2;
      }
      else {
          if (v==2) {
              v = 1;
          }
      }
      if ((i%6)==0) {
          v = v*v+v;
      }
      else {
          v = v*v;
      }
      if ((i%8)==0) {
          v = v*2;
      }
  }

}
