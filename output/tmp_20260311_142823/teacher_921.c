int main1(int k,int q){
  int i, u, o, r;

  i=59;
  u=i;
  o=0;
  r=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o % 4 == 0;
  loop invariant 0 <= o;
  loop invariant o <= i + 3;
  loop invariant r % 3 == 0;
  loop invariant -3*(o/4) <= r && r <= 3*(o/4);

  loop invariant r % 3 == 0 && -3*(o/4) <= r && r <= 3*(o/4) && k == \at(k, Pre) && q == \at(q, Pre);

  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant o >= 0;
  loop invariant o <= i + 1;
  loop invariant i == 59;

  loop invariant (o/4) <= 8 ==> r == 3*(o/4);

  loop invariant (o <= 4*(i/8)) ==> r == 3*(o/4);
  loop invariant -3*(o/4) <= r;
  loop invariant r <= 3*(o/4);
  loop invariant (o <= 32) ==> (r == 3*(o/4));
  loop assigns r, o;
*/
while (o<i) {
      if (o<i/2) {
          r = r+3;
      }
      else {
          r = r-3;
      }
      o = o+1;
      o = o+3;
  }
/*@
  assert !(o<i) &&
         (o % 4 == 0);
*/


}
