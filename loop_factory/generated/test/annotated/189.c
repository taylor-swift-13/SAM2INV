int main1(){
  int hp;
  hp=-7513;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (hp + 3) % 7510 == 0;
  loop invariant hp <= -7513;
  loop invariant hp % 2 != 0;
  loop assigns hp;
*/
while (hp<=-3) {
      hp = hp+hp+1;
      hp += 2;
  }
}