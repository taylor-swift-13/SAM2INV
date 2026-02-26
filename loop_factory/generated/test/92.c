int main92(int a,int n,int q){
  int x, g, v, f;

  x=(n%26)+16;
  g=0;
  v=x;
  f=x;

  while (1) {
      f = f+v;
      v = v*2;
  }

  while (g<f) {
      if (g<f) {
          g = g+1;
      }
      g = g+v;
      v = v+v;
      v = v+5;
      g = g*2;
  }

  while (x!=0&&f!=0) {
      if (x>f) {
          x = x-f;
      }
      else {
          f = f-x;
      }
      x = x*2;
  }

}
