int main1(){
  int eq, hh8, i, kl;

  eq=(1%60)+60;
  hh8=(1%9)+2;
  i=0;
  kl=0;

  while (1) {
      if (eq<=hh8*i+kl) {
          break;
      }
      if (kl==hh8-1) {
          kl = 0;
          i = i + 1;
      }
      else {
          kl += 1;
      }
      hh8 = (i)+(hh8);
  }

}
