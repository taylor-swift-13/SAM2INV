int main91(int a,int k,int n){
  int m, v, c, u, h;

  m=k+11;
  v=0;
  c=0;
  u=-8;
  h=-3;

  while (v<=m-3) {
      u = m-c;
      c = c+1;
      u = u+c;
      h = h+1;
  }

  while (u+1<=c) {
      if (m+5<=c) {
          m = m+5;
      }
      else {
          m = c;
      }
  }

  while (1) {
      if (u>=v) {
          break;
      }
      m = m+1;
      u = u+1;
      m = m+2;
      h = h+4;
      m = h-m;
  }


  /*@ assert (u>=v); */
}
