int main116(int a,int m,int n){
  int v, o, e, l, w;

  v=(n%39)+11;
  o=0;
  e=n;
  l=5;
  w=a;

  while (1) {
      e = e+4;
      e = e*2;
  }

  while (1) {
      l = l+o;
      o = o+w;
      l = l*l;
      e = e+o*l;
  }


  /*@ assert \false; */
}
