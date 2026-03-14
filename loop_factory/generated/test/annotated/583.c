int main1(){
  int m, f9j, un, w;
  m=1+3;
  f9j=0;
  un=0;
  w=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((un == 0) ==> (w == 16)) && ((un > 0) ==> (w == un + f9j));
  loop invariant 0 <= un <= m;
  loop invariant m == 1 + 3;
  loop invariant f9j == 0;
  loop assigns un, w;
*/
while (un<m) {
      if (un>=m/2) {
          w += 4;
      }
      un += 1;
      w = un+f9j;
  }
}