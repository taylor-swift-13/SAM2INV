int main61(int a,int m,int p){
  int o, t, d;

  o=p+8;
  t=o;
  d=o;

  while (t>=1) {
      d = d+3;
      d = d+5;
  }


  /*@ assert t < 1; */
}
