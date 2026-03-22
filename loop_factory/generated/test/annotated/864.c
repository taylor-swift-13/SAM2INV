int main1(int q){
  int at, jz, gbw, guh;
  at=q;
  jz=1;
  gbw=q;
  guh=at;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant at == \at(q, Pre);
  loop invariant at <= guh <= at + 1;
  loop invariant (gbw == at) || (gbw == guh*guh);
  loop invariant guh - at == (jz > 1);
  loop invariant jz == 1 || jz == at;
  loop invariant at == q;
  loop invariant (jz != 1) ==> (guh == at + 1);
  loop assigns guh, gbw, jz;
*/
while (jz<=at-1) {
      guh = guh + 1;
      gbw = guh*guh;
      jz = at;
  }
}