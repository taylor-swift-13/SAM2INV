int main28(int a,int b,int m){
  int u, e, z, h;

  u=32;
  e=0;
  z=a;
  h=-1;

  while (z!=0&&h!=0) {
      if (z>h) {
          z = z-h;
      }
      else {
          h = h-z;
      }
  }

}
