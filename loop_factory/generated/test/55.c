int main55(int k,int n,int q){
  int d, e, z, m;

  d=27;
  e=0;
  z=e;
  m=q;

  while (1) {
      m = m+z;
      while (1) {
          d = m-e;
          e = e+1;
          d = d-1;
          e = e+z;
      }
  }


  /*@ assert \false; */
}
