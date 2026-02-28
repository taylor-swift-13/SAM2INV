int main1(int a,int p){
  int h, o, v, l;

  h=44;
  o=0;
  v=3;
  l=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 3*(v - 3);
  loop invariant o % 3 == 0;
  loop invariant v >= 3;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant o <= h;
  loop invariant h == 44;
  loop invariant v == 3 + o/3;
  loop invariant 0 <= o;
  loop invariant o >= 0;
  loop invariant v <= 17;
  loop assigns o, v;
*/
while (o+3<=h) {
      v = v+1;
      o = o+3;
  }

}
