int main1(){
  int v50h, e4, z6ft;

  v50h=15;
  e4=3;
  z6ft=7;

  while (e4<v50h) {
      z6ft = e4%5;
      if (e4>=z6ft) {
          z6ft = (e4-z6ft)%5;
          z6ft = z6ft+z6ft-z6ft;
      }
      else {
          z6ft += z6ft;
      }
      e4 = e4 + 1;
      z6ft += 4;
  }

}
