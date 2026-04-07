int main1(int p){
  int d, c0, msv, lw7;
  d=(p%14)+17;
  c0=d;
  msv=c0;
  lw7=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant msv + c0 == 2 * (((\at(p,Pre) % 14) + 17));
  loop invariant lw7 + c0 == p + (((\at(p,Pre) % 14) + 17));
  loop invariant c0 + msv == 2*d;
  loop invariant lw7 - p == msv - d;
  loop invariant lw7 + c0 == p + d;
  loop invariant 0 <= c0 <= d;
  loop invariant lw7 - msv == p - d;
  loop assigns msv, c0, lw7;
*/
while (c0 > 0) {
      msv = msv + 1;
      c0--;
      lw7 = lw7 + 1;
  }
}