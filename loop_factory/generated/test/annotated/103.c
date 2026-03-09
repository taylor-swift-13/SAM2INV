int main1(int z,int o){
  int ji, yymw, vxmq, iie;
  ji=(z%19)+14;
  yymw=0;
  vxmq=0;
  iie=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yymw;
  loop invariant vxmq == ji * yymw;
  loop invariant 1 <= iie <= 20;
  loop invariant (ji >= 0) ==> (yymw <= ji);
  loop invariant (iie == 20 || iie <= yymw);
  loop assigns yymw, iie, vxmq;
*/
while (1) {
      if (!(yymw<=ji-1)) {
          break;
      }
      yymw += 1;
      if (yymw<=iie) {
          iie = yymw;
      }
      vxmq = vxmq + ji;
  }
}