int main1(int b,int q){
  int y, a, s;

  y=(q%39)+6;
  a=0;
  s=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == (\at(q,Pre) % 39) + 6;
  loop invariant s >= -6;
  loop invariant (b*b <= y+4) ==> s <= 6;
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant y == (q % 39) + 6;
  loop assigns s;
*/
while (1) {
      s = s+2;
      if (b*b<=y+4) {
          s = s%7;
      }
  }

}
