int main17(int a,int p,int q){
  int z, w, p1, z1, w1, p2;

  z=0;
  w=0;
  p1=0;
  z1=0;
  w1=0;
  p2=0;

  while (a>0) {
      z = z+p*p;
      w = w+q*q;
      p1 = p1+p*q;
      a = a-1;
      while (a>0) {
          z1 = z1+p*p;
          w1 = w1+q*q;
          p2 = p2+p*q;
          a = a-1;
      }
  }

}
