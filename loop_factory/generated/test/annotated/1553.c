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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (db == 2 * lp);
  loop invariant (d == 3 * lp);
  loop invariant (jzy == 7 + 4 * lp);
  loop invariant se <= f;
  loop invariant f <= se + lp;
  loop invariant lp <= f5;
  loop invariant f5 <= 2 * lp;
  loop invariant xhyd >= 13;
  loop invariant u7 >= 6;
  loop invariant v0 >= -5;
  loop invariant f5 == lp + ((lp + 1) / 2);
  loop invariant 0 <= lp <= se;
  loop invariant f >= 10;
  loop assigns xhyd, u7, v0, f, lp, db, f5, d, jzy;
*/
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