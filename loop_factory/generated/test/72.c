int main72(int m,int n,int p){
  int r, b, v;

  r=44;
  b=r+3;
  v=-4;

  while (b>=r+1) {
      v = v+4;
  }


  /*@ assert b < r+1; */
}
