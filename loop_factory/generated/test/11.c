int main11(int a,int b,int n){
  int l, u, v, c;

  l=(a%32)+14;
  u=l;
  v=-8;
  c=a;

  while (u>1) {
      v = v+1;
      c = c-1;
      v = v*2;
  }

  while (1) {
      l = l+4;
      l = l+l;
      while (c-1>=0) {
          u = u+9;
          v = v+9;
          u = u*3+4;
          v = v*u+4;
          v = v*2;
      }
  }


  /*@ assert c-1 < 0; */
}
