int main1(int q){
  int r, o, e, v;

  r=47;
  o=r;
  e=o;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 47;
  loop invariant o <= r;
  loop invariant o >= 0;
  loop invariant o % 2 == r % 2;
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= o;
  loop invariant o <= 47;
  loop invariant o % 2 == 47 % 2;
  loop invariant o + 2 * ((47 - o) / 2) == 47;
  loop invariant o >= 1;
  loop invariant o % 2 == 1;
  loop assigns o;
*/
while (o-2>=0) {
      o = o-2;
  }

}
