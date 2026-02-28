int main1(int b,int k){
  int y, u, x, r;

  y=61;
  u=0;
  x=0;
  r=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u <= y - 2;
  loop invariant x <= y;
  loop invariant (x == y) || (x % 3 == 0);
  loop invariant u == 0;
  loop invariant y == 61;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= u;
  loop invariant (x % 3 == 0) || (x == y);
  loop invariant 0 <= x;
  loop invariant (x == y) || (x % 3 == 0 && x <= 60);
  loop invariant 0 <= x <= y;
  loop invariant u <= y - 1;
  loop assigns x;
*/
while (u<=y-2) {
      if (x+3<=y) {
          x = x+3;
      }
      else {
          x = y;
      }
  }

}
