int main1(){
  int tyix, ywn, o, xp1p;
  tyix=53;
  ywn=0;
  o=ywn;
  xp1p=tyix;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xp1p == 53;
  loop invariant tyix >= ywn + 5;
  loop invariant o >= ywn;
  loop invariant ywn == 0;
  loop assigns o, tyix, xp1p;
*/
while (ywn+6<=tyix) {
      if (!(!(o+3<=tyix))) {
          o = o + 3;
      }
      else {
          o = tyix;
      }
      xp1p = xp1p+o-o;
      tyix = (ywn+6)-1;
  }
}