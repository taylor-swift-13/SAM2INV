int main40(int k,int p,int q){
  int m, g, w;

  m=k+11;
  g=0;
  w=-3;

  while (g+1<=m) {
      w = w*w;
      if (g+7<=p+m) {
          w = w*w;
      }
      w = w*w+w;
      g = g+1;
  }

  while (w>0) {
      w = w/2;
  }

}
