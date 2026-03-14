int main1(){
  int g, hg, c1, sy1, t;

  g=45;
  hg=0;
  c1=0;
  sy1=0;
  t=0;

  while (hg<=g-1) {
      t += 1;
      sy1 = sy1 + 1;
      if (sy1>=7) {
          sy1 = sy1 - 7;
          c1++;
      }
      hg = hg + 1;
  }

}
