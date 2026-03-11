int main1(){
  int xg, jxfp, cs, imqz, ch;
  xg=1+12;
  jxfp=0;
  cs=0;
  imqz=jxfp;
  ch=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cs >= 0;
  loop invariant cs % 8 == 0;
  loop invariant (cs == 0) <==> (imqz == 0);
  loop invariant (cs >= 8) ==> (imqz + cs == xg + 8);
  loop invariant jxfp == 0;
  loop invariant cs <= xg + 7;
  loop invariant ch == (cs / 8) * jxfp;
  loop assigns imqz, cs, ch;
*/
while (cs<=xg-1) {
      imqz = xg-cs;
      cs += 8;
      ch += jxfp;
  }
}