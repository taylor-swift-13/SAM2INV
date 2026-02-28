int main82(int m,int n,int p){
  int z, f, w, q;

  z=(n%39)+14;
  f=0;
  w=n;
  q=5;

  while (1) {
      w = w+1;
      q = q-1;
      while (z+4<=w) {
          if (f+2<=w) {
              f = f+2;
          }
          else {
              f = w;
          }
      }
  }


  /*@ assert z+4 > w; */
}
