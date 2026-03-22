int main1(){
  int e, hp, m, pz;
  e=1*3;
  hp=0;
  m=hp;
  pz=hp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pz == 0;
  loop invariant 0 <= hp;
  loop invariant hp <= e;
  loop invariant m == pz * hp;
  loop assigns m, hp;
*/
while (1) {
      m += pz;
      hp = hp + 1;
      if (hp>=e) {
          break;
      }
  }
}