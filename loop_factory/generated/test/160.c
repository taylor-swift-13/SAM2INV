int main160(int a,int b,int m){
  int w, k, d;

  w=b-7;
  k=w;
  d=8;

  while (k-1>=0) {
      d = d+2;
      d = d-w;
  }

  while (d-2>=0) {
      w = w+3;
      if (d+3<=m+k) {
          w = w+1;
      }
      if (m<k+2) {
          w = w-w;
      }
  }

}
