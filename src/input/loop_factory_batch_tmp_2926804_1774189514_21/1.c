int main1(int g){
  int nyw, e3g, g0, z1, nx27, o, go, hs0, r, m9it;

  nyw=(g%15)+7;
  e3g=nyw+6;
  g0=0;
  z1=0;
  nx27=0;
  o=(g%18)+5;
  go=nyw;
  hs0=e3g;
  r=g;
  m9it=g;

  while (o>0) {
      o--;
      z1 = z1+g*g;
      nx27 = nx27+g*g;
      g0 = g0+g*g;
      if ((e3g%7)==0) {
          m9it = m9it*hs0;
      }
      if (go+5<nyw) {
          go = go*g;
      }
      go = go*3+5;
      g = g + z1;
      hs0 = hs0 + nx27;
      r = r + 1;
      hs0 = hs0*go+5;
  }

}
