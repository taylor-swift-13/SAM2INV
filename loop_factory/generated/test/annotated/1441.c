int main1(int g){
  int y0q, br, sbs, qt9, fm;
  y0q=76;
  br=y0q;
  sbs=0;
  qt9=br;
  fm=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (br < 76) ==> (sbs == br + 2);
  loop invariant (br < 76) ==> (fm == br - 1);
  loop invariant (br < 76) ==> ((qt9 - fm) == 2);
  loop invariant 0 <= br;
  loop assigns br, sbs, qt9, fm;
*/
while (br > 0) {
      br = br - 1, sbs = br - 1, qt9 = br - 1, fm = br - 1;
      qt9 += 2;
      sbs = sbs + 3;
  }
}