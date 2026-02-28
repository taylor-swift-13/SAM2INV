int main100(int m,int n,int q){
  int l, k, o, d, w;

  l=m+12;
  k=0;
  o=1;
  d=-1;
  w=q;

  while (k+2<=l) {
      o = o+1;
      d = d+o;
      k = k+2;
  }

  while (1) {
      l = l+4;
      k = k+4;
      l = l*4;
      k = k/4;
      k = l*l;
  }


  /*@ assert \false; */
}
