int main1(int o){
  int hb, t, ced, rb;

  hb=19;
  t=0;
  ced=0;
  rb=0;

  while (t+1<=hb) {
      ced = ced + 1;
      rb += ced;
      hb = (t+1)-1;
  }

  while (rb<=t-1) {
      hb = t-rb;
      o += ced;
      rb += 1;
  }

}
