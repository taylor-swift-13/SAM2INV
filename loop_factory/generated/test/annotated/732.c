int main1(){
  int uuj, bff, afnz;
  uuj=0;
  bff=(1%28)+10;
  afnz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant afnz == uuj*(uuj+1)/2;
  loop invariant bff == 11 - uuj*(uuj-1)/2;
  loop assigns afnz, bff, uuj;
*/
while (1) {
      if (!(bff>uuj)) {
          break;
      }
      bff -= uuj;
      uuj++;
      afnz += uuj;
  }
}