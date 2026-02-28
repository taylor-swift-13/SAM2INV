int main86(int b,int k,int p){
  int r, u, d, v, w;

  r=b;
  u=r+5;
  d=0;
  v=b;
  w=k;

  while (d<r) {
      d = d+1;
      if (d<=w) {
          w = d;
      }
      d = d*2+4;
  }

  while (u<d) {
      if (r<=w) {
          w = r;
      }
      v = v+1;
      v = v+3;
      w = w+v;
      r = r+w;
  }


  /*@ assert u >= d; */
}
