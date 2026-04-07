int main1(){
  int x2, kk, yu4d, eyxx, pe7, r7;
  x2=1+12;
  kk=0;
  yu4d=kk;
  eyxx=2;
  pe7=4;
  r7=x2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yu4d == kk * r7;
  loop invariant eyxx == 2 + (r7 * kk * (kk + 1)) / 2;
  loop invariant pe7 == 4 + kk * x2;
  loop invariant 0 <= kk <= x2;
  loop invariant r7 == 13;
  loop invariant x2 == 13;
  loop invariant pe7 == 4 + x2 * kk;
  loop assigns yu4d, kk, eyxx, pe7;
*/
while (kk < x2) {
      yu4d = yu4d + r7;
      kk++;
      eyxx += yu4d;
      pe7 += x2;
  }
}