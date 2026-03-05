int main1(){
  int r39, psw, c;
  r39=(1%9)+16;
  psw=0;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 4 * psw;
  loop invariant psw <= r39;
  loop invariant psw >= 0;
  loop invariant r39 == (1%9)+16;
  loop assigns c, psw;
*/
while (psw<r39) {
      if (psw%2==0) {
          if (c>0) {
              c--;
              c = c + 1;
          }
      }
      else {
          if (c>0) {
              c--;
              c = c + 1;
          }
      }
      psw++;
      c += 4;
  }
}