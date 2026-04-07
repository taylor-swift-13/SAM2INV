int main1(int v){
  int jo3, z, a, mnsr;

  jo3=v*5;
  z=0;
  a=0;
  mnsr=v;

  while (1) {
      if (!(z < jo3)) {
          break;
      }
      z += 1;
      a += mnsr;
      mnsr = mnsr+a-a;
  }

}
