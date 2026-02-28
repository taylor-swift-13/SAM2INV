int main199(int b,int m,int n){
  int z, i, t, a;

  z=n-4;
  i=0;
  t=z;
  a=m;

  while (t!=0&&a!=0) {
      if (t>a) {
          t = t-a;
      }
      else {
          a = a-t;
      }
      t = t+1;
  }


  /*@ assert t == 0&&a!=0; */
}
