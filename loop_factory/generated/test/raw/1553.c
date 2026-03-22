int main1(){
  int se, lp, xhyd, f5, u7, d, v0, jzy, db, f;

  se=(1%15)+9;
  lp=0;
  xhyd=13;
  f5=lp;
  u7=6;
  d=lp;
  v0=-5;
  jzy=7;
  db=lp;
  f=se;

  while (1) {
      if (!(lp < se)) {
          break;
      }
      if (!(!(lp % 2 == 0))) {
          xhyd = xhyd + f5;
      }
      else {
          u7 += d;
      }
      if (lp % 3 == 0) {
          v0 += db;
      }
      if (f < jzy) {
          f = f + 1;
      }
      lp++;
      db += 2;
      f5 = f5+(lp%2);
      d = d + 3;
      f5 += 1;
      jzy += 4;
  }

}
