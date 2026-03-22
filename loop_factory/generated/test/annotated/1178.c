int main1(){
  int rso, x, pqy, h;
  rso=(1%60)+60;
  x=(1%9)+2;
  pqy=0;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rso >= x*pqy + h;
  loop invariant 0 <= h <= x - 1;
  loop invariant 0 <= pqy;
  loop assigns h, pqy, rso;
*/
while (1) {
      if (rso<=x*pqy+h) {
          break;
      }
      if (h==x-1) {
          h = 0;
          pqy++;
      }
      else {
          h += 1;
      }
      rso = ((pqy%2))+(rso);
  }
}