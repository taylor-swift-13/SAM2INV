int main1(int q){
  int fje, qvk, x, ya, dxvj;
  fje=33;
  qvk=0;
  x=fje;
  ya=qvk;
  dxvj=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 33 - 3*ya;
  loop invariant q == \at(q,Pre) + 33*qvk - (3*qvk*(qvk+1))/2;
  loop invariant qvk == ya;
  loop invariant x == fje + dxvj * qvk;
  loop invariant q == \at(q,Pre) + qvk * fje + dxvj * qvk * (qvk + 1) / 2;
  loop invariant 0 <= qvk;
  loop invariant ya <= fje;
  loop assigns q, x, ya, qvk;
*/
while (1) {
      if (!(qvk < fje)) {
          break;
      }
      x += dxvj;
      ya += 1;
      qvk += 1;
      q += x;
  }
}