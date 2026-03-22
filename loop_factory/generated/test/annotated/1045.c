int main1(){
  int ve, g, ex, ffw;
  ve=1;
  g=0;
  ex=0;
  ffw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 0;
  loop invariant ffw == ex*(ex+1)/2;
  loop invariant ve >= g;
  loop invariant ex >= 0;
  loop assigns ex, ffw, ve;
*/
while (g+1<=ve) {
      ex += 1;
      ffw = ffw + ex;
      ve = (g+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ve == 0;
  loop invariant g % 6 == 0;
  loop invariant g >= 0;
  loop invariant ve >= g;
  loop assigns g;
*/
while (g-6>=0) {
      g -= 6;
  }
}