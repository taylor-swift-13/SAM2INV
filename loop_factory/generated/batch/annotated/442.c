int main1(int b,int m){
  int r, u, v;

  r=(b%30)+15;
  u=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (((\at(b, Pre)) % 30) + 15);
  loop invariant u == 0;

  loop invariant r == (b % 30) + 15;
  loop invariant v >= m;

  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (r >= 2) ==> ((v - m) % 4 == 0);
  loop assigns v;
*/
while (1) {
      v = v+2;
      if ((u%5)==0) {
          v = v+1;
      }
      if (u+4<=r+r) {
          v = v+1;
      }
  }

}
