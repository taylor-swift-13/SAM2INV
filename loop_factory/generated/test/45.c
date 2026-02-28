int main45(int a,int m,int q){
  int o, u, v, i;

  o=q+13;
  u=0;
  v=q;
  i=-4;

  while (u+1<=o) {
      v = v+4;
      i = i+i;
      i = i+v;
      v = v+1;
  }

  while (v+2<=o) {
      u = u*2;
      i = i+u;
      v = v+2;
  }

  while (u*2<=v) {
      o = o+1;
      i = i+1;
      o = o*o+o;
      o = o%8;
      i = i*o;
  }


  /*@ assert u*2 > v; */
}
