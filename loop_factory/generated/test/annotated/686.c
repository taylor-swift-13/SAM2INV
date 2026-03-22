int main1(){
  int acnw, o, zrd, z;
  acnw=(1%27)+4;
  o=(1%40)+2;
  zrd=0;
  z=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant acnw == 5;
  loop invariant zrd >= 0;
  loop invariant z == 16;
  loop invariant (o == 2) || (o == 3);
  loop assigns zrd, o, z;
*/
while (o!=zrd) {
      zrd = o;
      o = (o+acnw/o)/2;
      z = z+(o%2);
  }
}