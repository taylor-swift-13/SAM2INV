int main1(int l,int r){
  int y2h, mc, q1, sp9a, zj;

  y2h=52;
  mc=0;
  q1=0;
  sp9a=0;
  zj=mc;

  while (sp9a<y2h) {
      sp9a = sp9a + 1;
      q1 += l;
      l += 2;
      r = r + y2h;
  }

  while (1) {
      if (!(zj<q1)) {
          break;
      }
      zj = zj + 1;
      y2h += l;
      l = l + 1;
      r = r+(y2h%8);
  }

}
