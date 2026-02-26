int main140(int k,int p,int q){
  int m, z, l;

  m=q;
  z=1;
  l=m;

  while (z<=m/2) {
      l = l+2;
      if (l*l<=m+3) {
          l = l%3;
      }
      l = l*l+l;
  }

}
