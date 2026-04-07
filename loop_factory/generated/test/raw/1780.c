int main1(){
  int o, svz1, r163, dgg;

  o=(1%60)+60;
  svz1=(1%9)+2;
  r163=0;
  dgg=0;

  while (1) {
      if (o<=svz1*r163+dgg) {
          break;
      }
      if (dgg==svz1-1) {
          dgg = 0;
          r163++;
      }
      else {
          dgg = dgg + 1;
      }
      o = (dgg)+(o);
  }

}
