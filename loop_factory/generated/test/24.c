int main24(int b,int n,int q){
  int t, h, v, x;

  t=58;
  h=0;
  v=-4;
  x=t;

  while (h<t) {
      x = x+v;
  }

  while (h>=2) {
      v = v+4;
  }


  /*@ assert h < 2; */
}
