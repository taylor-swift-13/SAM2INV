int main1(int x,int y){
  int f, fx, z, o1, cfrt;

  f=0;
  fx=0;
  z=0;
  o1=(y%18)+5;
  cfrt=0;

  while (o1>=1) {
      o1 -= 1;
      f = f+x*x;
      fx = fx+y*y;
      z = z+x*y;
      cfrt = cfrt+(fx%9);
  }

}
