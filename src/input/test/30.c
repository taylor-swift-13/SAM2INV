int main30(int b,int p,int q){
  int l, v, g;

  l=p;
  v=1;
  g=2;

  while (v<l) {
      if (g==1) {
          g = 2;
      }
      else {
          if (g==2) {
              g = 1;
          }
      }
  }

}
