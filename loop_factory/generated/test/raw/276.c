int main1(){
  int qk, lrg, hqk, akt, eo5, mjqx;

  qk=1*2;
  lrg=0;
  hqk=27;
  akt=0;
  eo5=1;
  mjqx=0;

  while (hqk>0&&lrg<qk) {
      if (hqk<=eo5) {
          mjqx = hqk;
      }
      else {
          mjqx = eo5;
      }
      lrg++;
      hqk -= mjqx;
      akt += mjqx;
      eo5++;
  }

}
