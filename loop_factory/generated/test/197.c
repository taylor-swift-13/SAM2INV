int main197(int b,int n,int q){
  int x, v, s, p, j;

  x=53;
  v=0;
  s=q;
  p=b;
  j=x;

  while (1) {
      s = s+2;
  }

  while (s<v) {
      if (s<v) {
          s = s+1;
      }
  }

  while (v!=0&&j!=0) {
      if (v>j) {
          v = v-j;
      }
      else {
          j = j-v;
      }
      v = v*3;
      j = j/3;
      v = v%2;
      v = v*j;
  }


  /*@ assert v == 0&&j!=0; */
}
