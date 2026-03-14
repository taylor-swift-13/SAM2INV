int main1(){
  int xf, a, z, luh, qsoq, x;

  xf=1;
  a=0;
  z=0;
  luh=0;
  qsoq=0;
  x=4;

  while (a<xf) {
      luh = a%5;
      if (!(!(a>=x))) {
          qsoq = (a-x)%5;
          z = z+luh-qsoq;
      }
      else {
          z = z + luh;
      }
      a++;
      x = x+(a%2);
  }

}
