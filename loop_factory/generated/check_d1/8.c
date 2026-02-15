int main8(int m,int p,int q){
  int z, w, p1;

  z=0;
  w=0;
  p1=0;

  while (p>0) {
      z = z+m*m;
      w = w+q*q;
      p1 = p1+m*q;
      p = p-1;
  }

}
