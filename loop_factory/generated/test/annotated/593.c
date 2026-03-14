int main1(){
  int hbu, dj, auwh;
  hbu=0;
  dj=(1%20)+10;
  auwh=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dj + auwh + hbu == 20;
  loop invariant 0 <= hbu;
  loop invariant hbu <= 20;
  loop invariant (0 <= auwh);
  loop invariant dj == 11 - ((hbu + 1) / 2);
  loop assigns hbu, dj, auwh;
*/
for (; dj>0&&auwh>0; hbu++) {
      if (hbu%2==0) {
          dj = dj - 1;
      }
      else {
          auwh = auwh - 1;
      }
  }
}