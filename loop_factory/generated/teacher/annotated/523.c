int main1(int a,int q){
  int e, k, g;

  e=(a%28)+12;
  k=0;
  g=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e == a % 28 + 12;
  loop invariant (g + 6) % 14 == 0;
  loop invariant g >= 8;
  loop invariant e == (a % 28) + 12;
  loop invariant g % 2 == 0;
  loop invariant e == (\at(a, Pre) % 28) + 12;
  loop assigns g;
*/
while (1) {
      g = g+3;
      g = g+g;
  }

}
