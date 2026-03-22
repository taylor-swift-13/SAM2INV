int main1(int d,int l){
  int x4, e2, ln, s5f, bbn, ub;

  x4=16;
  e2=4;
  ln=1;
  s5f=0;
  bbn=-3;
  ub=8;

  while (1) {
      if (!(s5f<x4)) {
          break;
      }
      s5f = s5f + 1;
      ln += d;
      bbn = bbn + 1;
      ub = ub+(s5f%2);
  }

  while (ln+1<=x4) {
      ub = ub + e2;
      e2 += s5f;
      l = l+(ub%2);
      x4 = (ln+1)-1;
  }

}
