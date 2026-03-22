int main1(){
  int ek, w3, ia1, yla, a, yu, jd;
  ek=1+4;
  w3=ek;
  ia1=0;
  yla=1;
  a=6;
  yu=0;
  jd=w3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yu;
  loop invariant yu <= ek + 1;
  loop invariant jd == ek + ia1 + yu*yu + 5*yu;
  loop invariant a == 6 + 2*yu;
  loop invariant yla == 1 + yu*yu + 5*yu;
  loop invariant jd == 5 + yu*(yu*yu + 9*yu + 11)/3;
  loop invariant ia1 == yu*(yu*yu + 6*yu - 4) / 3;
  loop invariant jd == ek + yu*(yu*yu + 9*yu + 11) / 3;
  loop assigns ia1, yu, yla, jd, a;
*/
while (yu<=ek) {
      ia1 += yla;
      yu++;
      yla = yla + a;
      jd += yla;
      a += 2;
  }
}