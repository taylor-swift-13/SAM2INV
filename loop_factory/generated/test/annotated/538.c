int main1(){
  int sdn, c, s, ui, lw;
  sdn=1*3;
  c=0;
  s=0;
  ui=3;
  lw=sdn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c + ui == sdn;
  loop invariant lw == sdn + c*(c+1)/2;
  loop invariant (s == sdn * c - (c * (c - 1)) / 2);
  loop invariant 0 <= c;
  loop invariant c <= sdn;
  loop assigns s, c, lw, ui;
*/
while (c<sdn&&ui>0) {
      s += ui;
      c = c + 1;
      lw = lw + c;
      ui--;
  }
}