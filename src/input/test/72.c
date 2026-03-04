int main72(int m,int p,int q){
  int v, g, b;

  v=m+4;
  g=1;
  b=2;

  while (g<=v/2) {
      if (b==1) {
          b = 2;
      }
      else {
          if (b==2) {
              b = 1;
          }
      }
      b = b*b;
      b = b%2;
  }

}
