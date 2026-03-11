int main1(int b,int m){
  int r, u, v;

  r=(b%30)+15;
  u=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (b % 30) + 15;
  loop invariant u >= 0;
  loop invariant (u <= r) || (r < 0);
  loop invariant v % 5 == 0;
  loop invariant v <= -5;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == ((\at(b, Pre) % 30) + 15);
  loop invariant 0 <= u;

  loop invariant u <= 44;
  loop assigns u, v;
*/
while (u<r) {
      if ((u%5)==0) {
          v = v+v;
      }
      u = u+1;
  }

}
