int main1(int k,int p){
  int x, w, o;

  x=p+8;
  w=0;
  o=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x == p + 8;
  loop invariant o >= 4;
  loop invariant x == p + 8 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant o >= 4 && x == p + 8;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);

  loop invariant x == p + 8 && p == \at(p, Pre) && k == \at(k, Pre);
  loop invariant k == \at(k, Pre) && p == \at(p, Pre) && x == p + 8;
  loop assigns o;
*/
while (1) {
      o = o+2;
      o = o*o+o;
  }

}
