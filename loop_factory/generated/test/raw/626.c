int main1(){
  int qny, e7, ewd, chcj;

  qny=1;
  e7=0;
  ewd=2;
  chcj=1;

  while (e7<=qny-1) {
      if (ewd>=9) {
          chcj = -1;
      }
      if (ewd<=2) {
          chcj = 1;
      }
      ewd += chcj;
      e7 = e7 + 1;
  }

}
