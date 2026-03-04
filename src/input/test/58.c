int main58(int b,int p,int q){
  int u, v, d;

  u=(p%23)+6;
  v=0;
  d=2;

  while (1) {
      if (d==1) {
          d = 2;
      }
      else {
          if (d==2) {
              d = 1;
          }
      }
      d = d+d;
  }

  while (v+4<=d) {
      if (u==1) {
          u = 2;
      }
      else {
          if (u==2) {
              u = 1;
          }
      }
  }

}
