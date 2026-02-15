int main2(int m,int n,int q){
  int i, j, s, i1, j1, s1;

  i=0;
  j=0;
  s=0;
  i1=0;
  j1=0;
  s1=0;

  while (i<n) {
      j = 0;
      while (j<i) {
          s = s+j;
          j = j+1;
      }
      i = i+1;
  }

  while (i1<m) {
      j1 = 0;
      while (j1<i1) {
          s1 = s1+j1;
          j1 = j1+1;
      }
      i1 = i1+1;
  }

}
