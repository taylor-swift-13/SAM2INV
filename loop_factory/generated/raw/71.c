int main71(int a,int k,int n){
  int b, l, w, f, r;

  b=46;
  l=b;
  w=a;
  f=k;
  r=-8;

  while (l-1>=0) {
      w = w+1;
      f = f+w;
  }

  while (b<r) {
      f = f+2;
  }

  while (b<f) {
      if (w<=l) {
          l = w;
      }
      r = r+1;
  }

}
