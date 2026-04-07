int main1(int m){
  int yo, ea, kt, du1, nrg;

  yo=m-8;
  ea=0;
  kt=0;
  du1=ea;
  nrg=ea;

  while (1) {
      if (kt>=yo) {
          break;
      }
      if (nrg<=du1) {
          du1 = nrg;
      }
      nrg += ea;
      kt++;
  }

}
