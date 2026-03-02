int main1(int b,int p){
  int r, w, o;

  r=p;
  w=0;
  o=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 0 && r == p;
  loop invariant p == \at(p, Pre) && b == \at(b, Pre) && o >= -8;
  loop invariant r == \at(p, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant w == 0;
  loop invariant (w % 9) == 0;
  loop invariant o >= -8;
  loop invariant r == \at(p, Pre) && w == 0 && (w % 9) == 0;
  loop invariant w == 0 && r == p && b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant r == p;
  loop invariant w % 9 == 0;
  loop invariant o >= -8 && w == 0;
  loop invariant r == p && b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant w == 0 && o >= -8;

  loop invariant o >= -8 && p == \at(p, Pre) && b == \at(b, Pre);
  loop invariant w == 0 && r == p && p == \at(p, Pre) && b == \at(b, Pre) && o >= -8;
  loop assigns o;
*/
while (1) {
      o = o+3;
      if ((w%9)==0) {
          o = o*o+o;
      }
      else {
          o = o%6;
      }
  }

}
