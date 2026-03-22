int main1(){
  int uhs, meh, jl, me;
  uhs=0;
  meh=0;
  jl=(1%28)+10;
  me=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant me <= -4;
  loop invariant (me % 4) == 0;
  loop invariant uhs == 0;
  loop invariant jl == 11 - meh*(meh - 1) / 2;
  loop invariant 0 <= meh <= 5;
  loop assigns jl, meh, me;
*/
while (1) {
      if (!(jl>meh)) {
          break;
      }
      jl -= meh;
      meh += 1;
      me += uhs;
      me = me*2;
  }
}