int main1(){
  int t, rg, e3s6, rb8e;

  t=1;
  rg=t;
  e3s6=0;
  rb8e=1;

  while (e3s6>0&&rb8e<=t) {
      if (e3s6>rb8e) {
          e3s6 = e3s6 - rb8e;
      }
      else {
          e3s6 = 0;
      }
      e3s6 = e3s6 + 1;
      rb8e = rb8e + 1;
      rg++;
  }

}
