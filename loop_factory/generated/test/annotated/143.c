int main1(){
  int elg, g, nme, iwi;
  elg=58;
  g=1;
  nme=3;
  iwi=9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (1 <= g);
  loop invariant (g <= elg);
  loop invariant elg == 58;
  loop invariant iwi == 9 + 6*(g - 1);
  loop invariant nme == 3 + 6*(g - 1);
  loop assigns iwi, nme, g;
*/
for (; g<elg; g++) {
      iwi += 6;
      nme += 6;
  }
}