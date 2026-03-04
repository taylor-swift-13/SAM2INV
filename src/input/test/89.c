int main89(int a,int b,int q){
  int r, k, v;

  r=q+3;
  k=r;
  v=1;

  while (k>2) {
      if (v==1) {
          v = 2;
      }
      else {
          if (v==2) {
              v = 1;
          }
      }
      v = v+v;
      if ((k%9)==0) {
          v = v+k;
      }
  }

}
