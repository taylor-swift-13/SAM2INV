int main1(int r){
  int u8wl, pay, qk, vnq, t3p3;
  u8wl=r;
  pay=0;
  qk=0;
  vnq=0;
  t3p3=u8wl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u8wl == \at(r, Pre);
  loop invariant 0 <= pay;
  loop invariant qk == (pay / 2);
  loop invariant vnq == (pay - qk);
  loop invariant t3p3 == (\at(r, Pre) + (pay * (pay + 1)) / 2);
  loop invariant (u8wl < 0) || (pay <= u8wl);
  loop assigns pay, t3p3, qk, vnq;
*/
while (1) {
      if (!(pay < u8wl)) {
          break;
      }
      pay = pay + 1;
      t3p3 += pay;
      qk = qk + 1 - (pay % 2);
      vnq = vnq + (pay % 2);
  }
}