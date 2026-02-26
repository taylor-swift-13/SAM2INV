int main23(int m,int n,int q){
  int b, j, s;

  b=m;
  j=0;
  s=j;

  while (1) {
      if (s+3<b) {
          s = s*s;
      }
      j = j+1;
  }

  while (b>3) {
      s = s+3;
      s = s+1;
  }

  while (b>=1) {
      j = j+3;
      j = j+j;
      if ((b%8)==0) {
          j = j+1;
      }
      if (j+4<s) {
          j = j+b;
      }
      else {
          j = j+1;
      }
  }

}
