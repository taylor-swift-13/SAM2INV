int main1(int p,int c){
  int mu, r3, no, ge, sbj;

  mu=(p%31)+12;
  r3=mu;
  no=39;
  ge=1;
  sbj=0;

  while (no>0&&ge<=mu) {
      if (no>ge) {
          no -= ge;
      }
      else {
          no = 0;
      }
      ge = ge + 1;
      sbj++;
      r3 = r3 + 1;
  }

}
