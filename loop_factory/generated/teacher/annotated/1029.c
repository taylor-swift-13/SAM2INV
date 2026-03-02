int main1(int p,int q){
  int b, e, o;

  b=q;
  e=0;
  o=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == \at(q, Pre) && p == \at(p, Pre) && b == \at(q, Pre);
  loop invariant ((e == 0 && o == 5) || (e >= 1 && o == 6));
  loop invariant b == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e >= 0;
  loop invariant (o == 5 || o == 6) && e >= 0;
  loop invariant b == \at(q, Pre) && q == \at(q, Pre);

  loop invariant o == 5 || o == 6;
  loop invariant q == \at(q, Pre) && p == \at(p, Pre);
  loop assigns e, o;
*/
while (1) {
      o = o-o;
      o = o+6;
      e = e+1;
  }

}
