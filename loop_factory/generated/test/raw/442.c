int main1(){
  int pm, ca, oa, gaku, nu1t;

  pm=1+16;
  ca=3;
  oa=0;
  gaku=0;
  nu1t=pm;

  while (oa<pm) {
      gaku += oa;
      oa++;
      nu1t += ca;
  }

  while (1) {
      if (!(nu1t<gaku)) {
          break;
      }
      nu1t += 1;
  }

}
