int main1(){
  int sr5t, qxo, sjhh, m7, ufg, nbg, v;

  sr5t=1+4;
  qxo=sr5t;
  sjhh=6;
  m7=6;
  ufg=0;
  nbg=6;
  v=0;

  while (qxo<=sr5t-1) {
      if (qxo%3==0) {
          if (sjhh>0) {
              sjhh--;
              ufg++;
          }
      }
      else {
          if (sjhh<nbg) {
              sjhh = sjhh + 1;
              m7 += 1;
          }
      }
      v++;
      qxo += 1;
  }

}
