int main1(int d){
  int wip, ey, o;
  wip=24;
  ey=0;
  o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wip == 24;
  loop invariant d == \at(d, Pre);
  loop invariant (ey > 0) ==> (o > 0);
  loop invariant 0 <= ey <= wip;
  loop invariant 0 <= o <= 5;
  loop invariant (ey - o) % 5 == 0;
  loop invariant ey == 0 ==> o == 0;
  loop assigns o, ey;
*/
while (ey<wip) {
      o = o + 1;
      if (o>=6) {
          o -= 6;
          o = o + 1;
      }
      ey = ey + 1;
  }
}