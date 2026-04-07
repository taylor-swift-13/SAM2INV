int main1(){
  int ccl, am, a, txe, cm, ub, ngq, ih;

  ccl=(1%20)+15;
  am=0;
  a=am;
  txe=am;
  cm=ccl;
  ub=am;
  ngq=1;
  ih=-5;

  while (1) {
      if (!(am < ccl)) {
          break;
      }
      if ((am % 3) == 0) {
          a++;
      }
      if ((am % 3) == 1) {
          txe++;
      }
      if ((am % 3) == 2) {
          cm++;
      }
      else {
      }
      ub = ub + a;
      ih += cm;
      ngq += 2;
      am += 1;
      ngq = ngq + ih;
  }

}
