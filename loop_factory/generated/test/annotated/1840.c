int main1(){
  int ns3c, u5, ww28, ap, i8ni, uq;
  ns3c=53;
  u5=0;
  ww28=ns3c;
  ap=ns3c;
  i8ni=ns3c;
  uq=u5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ww28 == ns3c * (u5 + 1);
  loop invariant uq == ns3c * u5 * (u5 + 1) / 2;
  loop invariant i8ni == ns3c + (u5 * (u5 + 1)) / 2;
  loop invariant uq == ns3c * u5 + ap * u5 * (u5 - 1) / 2;
  loop invariant 0 <= u5;
  loop invariant u5 <= ns3c;
  loop invariant ap == ns3c;
  loop assigns uq, ww28, u5, i8ni;
*/
while (u5 < ns3c) {
      uq += ww28;
      ww28 = ww28 + ap;
      u5 += 1;
      i8ni += u5;
  }
}