int main1(){
  int ym, atl, oj2, yes6;
  ym=(1%8)+7;
  atl=ym;
  oj2=-5;
  yes6=ym;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yes6 == atl;
  loop invariant oj2 == -5 + (ym - atl);
  loop invariant ym == 8;
  loop invariant (0 <= atl && atl <= ym);
  loop assigns atl, yes6, oj2;
*/
while (atl>=1) {
      yes6 -= 1;
      oj2 = oj2 + 1;
      atl--;
  }
}