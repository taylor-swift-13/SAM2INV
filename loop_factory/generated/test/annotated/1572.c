int main1(int u){
  int uxp2, reu, jz4, g0, frw, b, ru, se, mg;
  uxp2=u;
  reu=0;
  jz4=6;
  g0=0;
  frw=u;
  b=uxp2;
  ru=uxp2;
  se=0;
  mg=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant se == 0;
  loop invariant jz4 + g0 == 6;
  loop invariant 0 <= reu;
  loop invariant (uxp2 >= 0) ==> (reu <= uxp2);
  loop invariant jz4 >= 0;
  loop invariant ru >= u;
  loop invariant 0 <= jz4;
  loop invariant 0 <= g0;
  loop invariant uxp2 == u;
  loop assigns reu, frw, ru, b, jz4, g0, se, mg;
*/
while (1) {
      if (!(reu<=uxp2-1)) {
          break;
      }
      if (!(!(reu%2==0))) {
          if (jz4>0) {
              jz4 -= 1;
              g0++;
          }
      }
      else {
          if (g0>0) {
              g0 -= 1;
              jz4++;
          }
      }
      frw = frw*3;
      ru = ru + g0;
      b = b/3;
      reu += 1;
      frw = frw*2;
      se = se*ru;
      if (se+7<uxp2) {
          mg = mg*mg+se;
      }
  }
}