int main1(int x){
  int w6, gh, t22s;
  w6=x;
  gh=0;
  t22s=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t22s == (gh % 2);
  loop invariant w6 == \at(x, Pre);
  loop invariant (gh == 0) ==> (x == \at(x, Pre));
  loop invariant (gh >= 1) ==> (x == 0);
  loop invariant 0 <= gh;
  loop invariant (w6 >= 0) ==> (gh <= w6);
  loop invariant (gh == 0 ==> x == \at(x, Pre)) && (gh > 0 ==> x == 0);
  loop assigns gh, t22s, x;
*/
while (gh < w6) {
      gh = gh + 1;
      t22s = 1 - t22s;
      x = x+(gh%2);
      x -= x;
  }
}