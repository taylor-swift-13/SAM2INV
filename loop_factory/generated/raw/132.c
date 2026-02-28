int main132(int k,int n,int q){
  int d, e, j, v, s;

  d=63;
  e=1;
  j=k;
  v=q;
  s=q;

  while (e*2<=d) {
      j = j+1;
      v = v+j;
      j = j*2;
      v = v+j;
      s = s%8;
  }

  while (s<=d-1) {
      e = d-v;
      v = v+1;
      v = v+e+j;
  }

  while (e+2<=d) {
      v = v+1;
      e = e+2;
  }

}
