int main112(int k,int m,int q){
  int v, y, t;

  v=32;
  y=v;
  t=5;

  while (y-3>=0) {
      t = t+3;
      t = t+t;
  }

  while (1) {
      t = t+4;
      if (t+6<y) {
          t = t%4;
      }
      else {
          t = t%5;
      }
  }

}
