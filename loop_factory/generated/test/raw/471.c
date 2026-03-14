int main1(int d){
  int u5, z, aj4, ko, mphv;

  u5=d+15;
  z=0;
  aj4=(d%18)+5;
  ko=(d%15)+3;
  mphv=aj4;

  while (aj4!=0) {
      aj4--;
      ko = ko - 1;
      d += z;
  }

  while (1) {
      if (!(z!=0)) {
          break;
      }
      u5 = u5 - 1;
      z = z - 1;
      mphv += z;
  }

}
