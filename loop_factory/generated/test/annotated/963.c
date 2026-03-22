int main1(){
  int so, wlcw;
  so=1+3;
  wlcw=so;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wlcw <= so;
  loop invariant so == 1 + 3;
  loop invariant wlcw >= 0;
  loop assigns wlcw;
*/
while (1) {
      if (!(wlcw>=1)) {
          break;
      }
      wlcw -= 1;
  }
}