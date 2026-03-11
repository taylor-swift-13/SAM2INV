int main1(){
  int i0, i, pox, ivr, sglm, nm9;

  i0=48;
  i=0;
  pox=0;
  ivr=0;
  sglm=20;
  nm9=5;

  while (1) {
      if (!(ivr<i0)) {
          break;
      }
      nm9 = nm9 + i0;
      pox++;
      sglm = sglm*2;
      ivr++;
  }

  while (ivr<=sglm-1) {
      nm9 = nm9 + 1;
      ivr++;
      i = i + sglm;
  }

}
