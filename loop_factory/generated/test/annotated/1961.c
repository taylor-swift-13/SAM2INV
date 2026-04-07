int main1(){
  int w, u4, b9, e6, b2;
  w=58;
  u4=w;
  b9=w;
  e6=8;
  b2=u4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b2 == 58;
  loop invariant b9 == b2;
  loop invariant u4 >= 1;
  loop invariant w == 58;
  loop invariant (e6 % b2) == 8;
  loop invariant u4 <= w;
  loop assigns b9, e6, u4;
*/
while (u4*u4>w) {
      b9 = (b9-b2)+(b9);
      e6 += b2;
      u4 = (u4+w/u4)/2;
  }
}