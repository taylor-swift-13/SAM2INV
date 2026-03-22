int main1(){
  int qy, cjd, o8, cmna;
  qy=(1%14)+13;
  cjd=0;
  o8=-2;
  cmna=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cjd + qy == 14;
  loop invariant o8 == -2 + cmna * cjd;
  loop invariant 0 <= cjd;
  loop invariant 0 <= qy;
  loop assigns cjd, o8, qy;
*/
while (1) {
      if (!(cjd < qy)) {
          break;
      }
      cjd += 1;
      o8 = o8 + cmna;
      qy--;
  }
}