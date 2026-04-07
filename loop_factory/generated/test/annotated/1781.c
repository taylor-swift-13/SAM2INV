int main1(int c){
  int dl, yqbv, z, e, bb84;
  dl=0;
  yqbv=(c%60)+60;
  z=(c%9)+2;
  e=0;
  bb84=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dl == 0;
  loop invariant c == \at(c, Pre);
  loop invariant 0 <= e;
  loop invariant z*e + bb84 <= yqbv;
  loop invariant yqbv == (\at(c, Pre) % 60) + 60;
  loop invariant z == (\at(c, Pre) % 9) + 2;
  loop assigns bb84, e, c;
*/
while (1) {
      if (yqbv<=z*e+bb84) {
          break;
      }
      if (bb84==z-1) {
          bb84 = 0;
          e += 1;
      }
      else {
          bb84++;
      }
      c = (dl)+(c);
  }
}