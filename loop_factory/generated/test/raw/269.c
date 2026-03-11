int main1(){
  int ij5, xp5, e, nlh;

  ij5=1*2;
  xp5=ij5;
  e=2;
  nlh=1;

  while (xp5<ij5) {
      if (e>=6) {
          nlh = -1;
      }
      if (e<=2) {
          nlh = 1;
      }
      xp5 = xp5 + 1;
      e += nlh;
  }

}
