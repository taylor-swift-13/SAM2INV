int main1(){
  int me, u, dh1, w, y6;
  me=1+24;
  u=me;
  dh1=(1%18)+5;
  w=(1%15)+3;
  y6=dh1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y6 + u*dh1 == 156;
  loop invariant dh1 - w == 2;
  loop invariant dh1 >= 0;
  loop invariant y6 == 156 - 25*dh1;
  loop assigns w, dh1, y6;
*/
while (dh1!=0) {
      w = w - 1;
      dh1 -= 1;
      y6 = y6 + u;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dh1 >= w;
  loop assigns dh1, u;
*/
while (w+1<=dh1) {
      u = u+me*w;
      dh1 = ((w+1))+(-(1));
  }
}