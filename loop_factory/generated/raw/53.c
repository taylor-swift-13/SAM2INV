int main53(int m,int n,int p){
  int t, u, h;

  t=m+6;
  u=0;
  h=p;

  while (1) {
      h = h+3;
      h = h+h;
      if (h+5<t) {
          h = h+h;
      }
      h = h+u;
  }

  while (h<u) {
      t = t+4;
      t = t%7;
      if ((h%5)==0) {
          t = t*2;
      }
      else {
          t = t*2;
      }
      if (t+6<u) {
          t = t*t;
      }
  }

}
