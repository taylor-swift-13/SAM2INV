int main1(){
  int sqvr, o9, kd, eot, g9j;
  sqvr=1+8;
  o9=0;
  kd=-6;
  eot=0;
  g9j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (o9 == 0) || (o9 == sqvr);
  loop invariant 0 <= o9;
  loop invariant o9 <= sqvr;
  loop invariant eot <= 0;
  loop invariant g9j >= 0;
  loop invariant kd == -6;
  loop invariant sqvr == 1 + 8;
  loop invariant g9j == 0;
  loop invariant (o9 == 0) ==> eot == 0;
  loop invariant (o9 == sqvr) ==> eot == kd;
  loop assigns eot, g9j, o9;
*/
while (1) {
      if (!(o9 < sqvr)) {
          break;
      }
      eot = (eot + kd < g9j ? eot + kd : (o9++, eot + kd - g9j));
      g9j += o9;
      o9 = sqvr;
  }
}