int main1(int c){
  int a7, zex, v, nb, bi1v;
  a7=79;
  zex=0;
  v=0;
  nb=0;
  bi1v=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bi1v == 5 - v;
  loop invariant 0 <= v;
  loop invariant v <= a7;
  loop invariant 0 <= bi1v;
  loop invariant nb == (v * (11 - v)) / 2;
  loop invariant c == \at(c, Pre);
  loop invariant zex == 0;
  loop assigns nb, v, c, bi1v;
*/
while (v<a7&&bi1v>0) {
      nb += bi1v;
      v++;
      c = c + zex;
      bi1v -= 1;
  }
}