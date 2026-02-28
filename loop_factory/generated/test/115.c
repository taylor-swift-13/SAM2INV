int main115(int a,int m,int n){
  int h, u, d, v, z;

  h=a;
  u=0;
  d=2;
  v=6;
  z=m;

  while (u<=h-2) {
      if (z<=v) {
          v = z;
      }
      d = d+1;
      d = d*2;
  }

  while (v!=0&&h!=0) {
      if (v>h) {
          v = v-h;
      }
      else {
          h = h-v;
      }
      v = v*2;
      h = h+v;
  }


  /*@ assert v == 0&&h!=0; */
}
