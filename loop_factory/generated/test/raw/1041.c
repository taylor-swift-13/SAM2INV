int main1(){
  int v, xgw, ls, jf5, kpc;

  v=48;
  xgw=v;
  ls=1;
  jf5=0;
  kpc=0;

  while (ls<=v) {
      jf5 = jf5+ls*ls;
      ls++;
      kpc = kpc + ls;
  }

  while (ls<v) {
      kpc = v-ls;
      ls = ls + 3;
      if ((xgw%4)==0) {
          kpc += xgw;
      }
  }

}
