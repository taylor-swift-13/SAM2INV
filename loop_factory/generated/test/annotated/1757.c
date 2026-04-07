int main1(){
  int lwe, nt4, oh, qwo, o9, gu;
  lwe=(1%39)+4;
  nt4=0;
  oh=-3;
  qwo=0;
  o9=13;
  gu=lwe;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lwe == 5;
  loop invariant qwo >= 0;
  loop invariant oh >= -3;
  loop invariant 0 <= nt4;
  loop invariant nt4 <= lwe;
  loop invariant o9 >= 13;
  loop invariant gu > 0;
  loop invariant (oh == -3) || (oh == 2*qwo);
  loop assigns nt4, o9, qwo, gu, oh;
*/
while (1) {
      if (!(nt4 < lwe)) {
          break;
      }
      nt4 = ((oh = (qwo += (o9 += gu))), (nt4 + 1));
      o9 += gu;
      gu = gu+gu+o9;
      oh = oh*2;
  }
}