int main1(int l,int n){
  int vld, eqvl, em, gns, e86;

  vld=45;
  eqvl=0;
  em=0;
  gns=8;
  e86=25;

  while (1) {
      if (!(em<=vld-1)) {
          break;
      }
      gns = em;
      em = em + 1;
      l += eqvl;
  }

  while (e86>0) {
      eqvl = eqvl+vld*e86;
      vld += em;
      e86 = 0;
  }

}
