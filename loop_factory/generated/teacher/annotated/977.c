int main1(int b,int p){
  int r, o, x;

  r=44;
  o=0;
  x=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 44 && o == 0 && (x == 44 || x == 0 || x == 1);
  loop invariant b == \at(b, Pre) && p == \at(p, Pre);
  loop invariant o == 0;
  loop invariant r == 44;
  loop invariant x == 44 || x == 0 || x == 1;
  loop invariant 0 <= x && x <= 44;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x >= 0;
  loop invariant x <= 44;
  loop invariant o % 7 == 0;
  loop invariant x == 44 || x < 2;
  loop invariant o == 0 && r == 44 && (x == 44 || x == 0 || x == 1);
  loop invariant r == 44 && b == \at(b, Pre) && p == \at(p, Pre) && (x == 44 || x == 1 || x == 0) && x >= 0 && x <= 44;
  loop assigns x;
*/
while (1) {
      x = x+3;
      if ((o%7)==0) {
          x = x%2;
      }
  }

}
