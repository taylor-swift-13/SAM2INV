int main1(int g,int m){
  int wu3g, ftqg, yz;
  wu3g=g;
  ftqg=wu3g;
  yz=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == wu3g * (ftqg - wu3g + 1);
  loop invariant yz == ftqg - wu3g - 8;
  loop invariant g - \at(g, Pre) == (ftqg - wu3g) * wu3g;
  loop invariant ftqg >= wu3g;
  loop invariant g - wu3g*ftqg == \at(g, Pre) - (\at(g, Pre)) * (\at(g, Pre));
  loop assigns g, ftqg, yz;
*/
while (ftqg-1>=0) {
      yz = yz + 1;
      g += wu3g;
      ftqg += 1;
  }
}