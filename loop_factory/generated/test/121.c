int main121(int b,int m,int n){
  int i, a, o, k, l;

  i=b-7;
  a=1;
  o=0;
  k=b;
  l=b;

  while (1) {
      k = i-o;
      o = o+1;
  }

  while (o<=k-2) {
      if (l+2<=k) {
          l = l+2;
      }
      else {
          l = k;
      }
      l = l*4;
  }


  /*@ assert o > k-2; */
}
