int main1(){
  int h61, wh6r, xy;
  h61=10;
  wh6r=0;
  xy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xy == 0;
  loop invariant xy <= h61;
  loop invariant wh6r <= h61;
  loop invariant (wh6r == 0) || (wh6r == h61);
  loop invariant 0 <= wh6r;
  loop invariant ((xy + wh6r) > h61)  ==> (xy == h61);
  loop assigns xy, wh6r;
*/
while (1) {
      if (!(wh6r < h61)) {
          break;
      }
      xy = ((xy + wh6r) <= h61) * (xy + wh6r) + ((xy + wh6r) > h61) * h61;
      wh6r = h61;
  }
}