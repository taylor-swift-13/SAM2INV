int main1(int c){
  int zp, r, of, tt, a8;

  zp=28;
  r=zp;
  of=1;
  tt=3;
  a8=r;

  while (1) {
      if (!(of<=zp)) {
          break;
      }
      tt = tt+of*of;
      a8 += r;
      of = of + 1;
      c = c + c;
  }

}
