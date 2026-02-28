int main151(int m,int n,int p){
  int b, k, t, v, z;

  b=p;
  k=0;
  t=p;
  v=8;
  z=n;

  while (k+1<=b) {
      v = t;
      t = t+1;
      t = t+2;
      z = z+3;
  }

  while (b!=0&&t!=0) {
      if (b>t) {
          b = b-t;
      }
      else {
          t = t-b;
      }
      b = b*2;
      t = t+b;
  }


  /*@ assert b == 0&&t!=0; */
}
