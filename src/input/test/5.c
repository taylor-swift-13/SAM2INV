int main5(int m,int n,int p){
  int z, x, v;

  z=(n%29)+10;
  x=1;
  v=1;

  while (1) {
      if (v==1) {
          v = 2;
      }
      else {
          if (v==2) {
              v = 1;
          }
      }
      v = v+v;
      v = v+1;
      if (x+7<=p+z) {
          v = v+4;
      }
  }

}
