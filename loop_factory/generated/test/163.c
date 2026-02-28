int main163(int a,int n,int q){
  int k, m, l, d, v;

  k=n;
  m=k;
  l=2;
  d=-8;
  v=-2;

  while (m>0) {
      l = l+10;
      d = d+10;
      l = l*2;
      d = d+l;
      v = v%4;
  }

  while (1) {
      if (d>=l) {
          break;
      }
      k = k+2;
      d = d+1;
      k = k*2+4;
      v = v*k+4;
  }


  /*@ assert (d>=l); */
}
