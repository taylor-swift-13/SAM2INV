int main1(int e,int y){
  int s, od, wpl;
  s=(y%14)+5;
  od=s;
  wpl=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == (\at(y, Pre) % 14) + 5;
  loop invariant od == s;
  loop invariant wpl <= -3;
  loop invariant e <= \at(e, Pre);
  loop invariant (e - 2*wpl) == (\at(e, Pre) + 6);
  loop invariant y == \at(y, Pre);
  loop invariant wpl % 3 == 0;
  loop assigns e, wpl;
*/
while (od>=3) {
      wpl = wpl + wpl;
      e = e + wpl;
  }
}