int main1(){
  int e6j, ci, r52, r06, a3;

  e6j=1*5;
  ci=0;
  r52=0;
  r06=0;
  a3=0;

  while (1) {
      if (!(ci<=e6j-1)) {
          break;
      }
      r06 = r06 + 1;
      a3++;
      if (r06>=9) {
          r06 = r06 - 9;
          r52++;
      }
      ci = ci + 1;
  }

}
