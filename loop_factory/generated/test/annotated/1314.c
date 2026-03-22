int main1(int w){
  int me, u0jy, yl;
  me=0;
  u0jy=(w%28)+10;
  yl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant me >= 0;
  loop invariant yl >= 0;
  loop invariant u0jy <= ((\at(w, Pre) % 28) + 10);
  loop invariant u0jy == ((w % 28) + 10) - me*(me - 1)/2;
  loop invariant yl % 2 == 0;
  loop invariant u0jy == ((w % 28) + 10) - ((me * (me - 1)) / 2);
  loop invariant u0jy == ((\at(w, Pre) % 28) + 10) - me*(me - 1)/2;
  loop assigns me, u0jy, yl;
*/
while (u0jy>me) {
      u0jy -= me;
      yl += u0jy;
      me = me + 1;
      yl = yl*2;
  }
}