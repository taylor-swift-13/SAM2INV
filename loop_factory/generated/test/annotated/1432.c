int main1(int o){
  int b95, yu, z;
  b95=(o%20)+5;
  yu=(o%20)+5;
  z=(o%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b95 == yu;
  loop invariant yu == z;
  loop invariant b95 <= ((\at(o, Pre) % 20) + 5);
  loop assigns b95, yu, z;
*/
while (b95>0) {
      if (yu>0) {
          if (z>0) {
              b95 -= 1;
              yu -= 1;
              z = z - 1;
          }
      }
  }
}