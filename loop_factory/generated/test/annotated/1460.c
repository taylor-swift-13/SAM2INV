int main1(){
  int px, w, u71, wbpc, yw;
  px=1*4;
  w=0;
  u71=0;
  wbpc=w;
  yw=px;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yw == px + u71*(u71+1)/2;
  loop invariant 0 <= u71;
  loop invariant u71 <= px;
  loop invariant wbpc <= yw;
  loop invariant wbpc == 0;
  loop assigns u71, wbpc, yw;
*/
while (u71<=px-1) {
      u71 += 1;
      if (!(!(yw<=wbpc))) {
          wbpc = yw;
      }
      yw = yw + u71;
  }
}