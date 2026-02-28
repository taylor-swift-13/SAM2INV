int main123(int a,int k,int n){
  int w, j, v, t;

  w=49;
  j=0;
  v=6;
  t=-6;

  while (j<w) {
      v = v*2+2;
      t = t*v+2;
      v = v+t;
  }

  while (t-1>=0) {
      w = j-v;
      v = v+1;
      w = w+v;
  }

  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      v = v*2;
      t = t/2;
      v = v*v+t;
      t = v*v;
  }


  /*@ assert v == 0&&t!=0; */
}
