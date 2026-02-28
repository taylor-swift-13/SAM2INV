int main6(int a,int m,int p){
  int h, u, v, b;

  h=m+5;
  u=2;
  v=0;
  b=u;

  while (u<=h-2) {
      b = h-v;
      v = v+1;
  }


  /*@ assert u > h-2; */
}
