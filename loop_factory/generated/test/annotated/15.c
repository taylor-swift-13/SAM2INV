int main1(){
  int y, ngr;
  y=-16845;
  ngr=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ngr + 5) % 3 == 0;
  loop invariant ngr >= -5;
  loop invariant 6*(y + 16845) == (ngr + 5)*(ngr - 2);
  loop assigns y, ngr;
*/
while (1) {
      if (!(y<=-3)) {
          break;
      }
      y = y+ngr+3;
      ngr += 2;
      ngr = ngr + 1;
  }
}