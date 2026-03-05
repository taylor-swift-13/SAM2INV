int main1(){
  int z1, z, d, kw;

  z1=1;
  z=2;
  d=z;
  kw=-2;

  while (z<z1) {
      if (z<z1/2) {
          d += kw;
      }
      else {
          d++;
      }
      kw = kw + z1;
  }

}
