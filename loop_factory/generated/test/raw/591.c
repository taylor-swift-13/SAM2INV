int main1(int w,int r){
  int db, zvv, a7n, x;

  db=w*4;
  zvv=0;
  a7n=6;
  x=1;

  while (1) {
      if (!(zvv<db)) {
          break;
      }
      zvv += 2;
      if (x<=a7n) {
          a7n = x;
      }
      x += a7n;
  }

}
