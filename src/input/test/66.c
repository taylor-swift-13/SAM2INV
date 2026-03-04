int main66(int a,int k,int m){
  int v, g, p;

  v=42;
  g=v+4;
  p=2;

  while (g-v>0) {
      if (p==1) {
          p = 2;
      }
      else {
          if (p==2) {
              p = 1;
          }
      }
      if ((g%2)==0) {
          p = p*p+p;
      }
  }

}
