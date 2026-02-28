int main31(int a,int k,int m){
  int e, o, v, u, q;

  e=m;
  o=0;
  v=6;
  u=k;
  q=k;

  while (1) {
      v = v+3;
      u = u+3;
      v = v+1;
  }

  while (o+1<=e) {
      q = q+v;
      v = v+q;
  }


  /*@ assert o+1 > e; */
}
