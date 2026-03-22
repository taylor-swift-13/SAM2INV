int main1(){
  int p, s, y, s2, mdd, ti, cn;
  p=1;
  s=p;
  y=0;
  s2=0;
  mdd=(1%50)+20;
  ti=(1%8)+2;
  cn=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= s2;
  loop invariant y >= 0;
  loop invariant cn >= 1;
  loop invariant 0 <= mdd <= 21;
  loop invariant s2 < ti;
  loop invariant ti > 0;
  loop assigns cn, mdd, s2, ti, y;
*/
while (1) {
      if (!(mdd!=0)) {
          break;
      }
      if (s2+1==ti) {
          y++;
          s2 = 0;
      }
      else {
          s2 = s2 + 1;
      }
      mdd--;
      ti = ti+(y%6);
      ti = ti*2;
      cn = cn + ti;
  }
}