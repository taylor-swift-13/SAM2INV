int main175(int b,int m,int q){
  int y, i, v;

  y=m;
  i=1;
  v=m;

  while (i<y) {
      v = v+2;
  }

  while (v+1<=y) {
      i = i+2;
      if (v+6<=i+y) {
          i = i%2;
      }
      else {
          i = i*i;
      }
      if (b*b<=y+4) {
          i = i+i;
      }
      i = i*i;
  }

  while (1) {
      y = y+2;
      y = y+y;
  }

}
