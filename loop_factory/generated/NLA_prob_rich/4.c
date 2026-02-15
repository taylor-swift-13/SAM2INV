int main4(int a,int k,int p){
  int z, w, p1, i, j, s;

  z=0;
  w=0;
  p1=0;
  i=0;
  j=0;
  s=0;

  while (a>0) {
      z = z+p*p;
      w = w+k*k;
      p1 = p1+p*k;
      a = a-1;
  }

  while (i<p) {
      j = 0;
      while (j<i) {
          s = s+j;
          j = j+1;
      }
      i = i+1;
  }

}
