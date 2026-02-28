int main109(int a,int b,int q){
  int v, t, o, p, w;

  v=b+24;
  t=1;
  o=v;
  p=4;
  w=-8;

  while (t<=v-1) {
      o = o+1;
      p = p+o;
  }


  /*@ assert t > v-1; */
}
