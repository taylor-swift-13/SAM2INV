int main81(int k,int m,int n){
  int d, u, r;

  d=m;
  u=0;
  r=m;

  while (u+1<=d) {
      r = r+3;
      if ((u%8)==0) {
          r = r*r;
      }
      else {
          r = r*r;
      }
  }

  while (1) {
      u = u+2;
      u = u%9;
      if (r+6<=r+d) {
          u = u*u+u;
      }
      u = u*u;
  }

  while (d<=r/2) {
      d = d*2;
  }

}
