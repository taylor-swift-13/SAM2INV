int main1(int k){
  int ymm, u09q, up, xd;

  ymm=(k%37)+8;
  u09q=ymm;
  up=0;
  xd=0;

  while (1) {
      if (!(u09q-1>=0)) {
          break;
      }
      xd = xd + up;
      u09q += 1;
  }

  while (xd<ymm) {
      u09q = u09q + k;
      xd++;
  }

}
