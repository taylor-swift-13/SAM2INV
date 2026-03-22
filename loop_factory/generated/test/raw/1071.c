int main1(){
  int cbs, z0, z5i;

  cbs=1;
  z0=-6;
  z5i=cbs;

  while (1) {
      if (!(z0+1<=cbs)) {
          break;
      }
      z0 += 1;
  }

  while (z5i>z0) {
      z5i -= z0;
      z0 += 1;
      cbs += z0;
  }

}
