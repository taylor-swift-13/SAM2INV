int main89(int a,int k,int n){
  int q, z, b, f;

  q=k+6;
  z=0;
  b=3;
  f=2;

  while (z+1<=q) {
      b = b*2;
      z = z+1;
  }

  while (1) {
      f = f+3;
      f = f+q;
      b = b*b;
      b = b+f*b;
      f = b+q;
  }


  /*@ assert \false; */
}
