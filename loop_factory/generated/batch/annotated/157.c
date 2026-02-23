int main1(int b){
  int a, u, g;

  a=10;
  u=a;
  g=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 10;
  loop invariant b == \at(b, Pre);
  loop invariant u <= 10;
  loop invariant (10 - u) % 3 == 0;
  loop invariant u % 3 == 1;
  loop invariant 1 <= u;
  loop invariant u <= a;
  loop invariant g >= a;
  loop invariant g >= u;
  loop invariant u >= 1;
  loop invariant g >= 10;
  loop invariant g % 10 == 0;
  loop assigns g, u;
*/
while (u>2) {
      g = g+g;
      u = u-3;
  }

}
