int main154(int a,int k,int p){
  int m, s, v, j, b;

  m=p;
  s=0;
  v=(p%20)+5;
  j=(p%20)+5;
  b=(p%20)+5;

  while (v>0) {
      if (j>0) {
          if (b>0) {
              v = v-1;
              j = j-1;
              b = b-1;
          }
      }
      v = v+1;
  }

  while (s!=0&&j!=0) {
      if (s>j) {
          s = s-j;
      }
      else {
          j = j-s;
      }
      s = s+j;
  }

  while (v<=m-5) {
      s = s+4;
      if (v+7<=s+m) {
          s = s+s;
      }
      else {
          s = s+v;
      }
      s = s+1;
  }


  /*@ assert v > m-5; */
}
