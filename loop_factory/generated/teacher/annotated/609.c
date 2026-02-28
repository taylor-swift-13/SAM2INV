int main1(int p,int q){
  int g, e, o, y;

  g=(p%18)+9;
  e=0;
  o=p;
  y=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == p + e;
  loop invariant (e % 2 == 0) ==> (y == -8);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e >= 0;
  loop invariant (e % 2 == 0) ==> y == -8;
  loop invariant g == ((\at(p, Pre)) % 18) + 9;
  loop invariant o - e == p;
  loop invariant o >= p;
  loop invariant g == ((\at(p,Pre) % 18) + 9);
  loop invariant y == -8 + 16*(e % 2);
  loop invariant g == (p % 18) + 9;
  loop assigns o, y, e;
*/
while (1) {
      o = o+1;
      y = y+o;
      y = o-y;
      e = e+1;
  }

}
