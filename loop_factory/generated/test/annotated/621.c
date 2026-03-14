int main1(){
  int sr, vy, fh, rji, mp;
  sr=(1%24)+14;
  vy=sr;
  fh=19;
  rji=1;
  mp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mp == rji - 1;
  loop invariant vy == sr + mp;
  loop invariant 0 <= mp;
  loop invariant mp <= sr;
  loop invariant fh <= 19;
  loop assigns fh, mp, rji, vy;
*/
while (fh>0&&rji<=sr) {
      if (!(fh<=rji)) {
          fh = 0;
      }
      else {
          fh = fh - rji;
      }
      mp += 1;
      vy += 1;
      rji++;
  }
}