int main1(int b,int p){
  int a, o, r;

  a=p+23;
  o=a;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((o == a && a == p + 23) || (o >= 0 && r == p + o + 1));
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant a == p + 23;
  loop invariant o <= a;
  loop invariant r == b || r == p + o + 1;

  loop invariant (o == a) ==> (r == b) && (o < a) ==> (r == p + o + 1);
  loop invariant p == \at(p, Pre) && b == \at(b, Pre) && o >= 0 && (o < p + 23) ==> (r == p + o + 1);
  loop invariant (r == \at(b, Pre) && o == \at(p, Pre) + 23) || (r == p + o + 1);

  loop invariant o <= \at(p, Pre) + 23;
  loop assigns r, o;
*/
while (o>0) {
      r = r+o;
      r = p+o;
      o = o-1;
  }

}
