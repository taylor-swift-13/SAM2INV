int main1(){
  int r2, cd, cu9, imc, ge;

  r2=19;
  cd=r2+6;
  cu9=0;
  imc=(1%28)+10;
  ge=cd;

  while (imc>cu9) {
      imc = imc - cu9;
      cu9 = cu9 + 1;
      ge = ge+(imc%7);
  }

}
