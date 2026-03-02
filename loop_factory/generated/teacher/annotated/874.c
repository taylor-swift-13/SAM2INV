int main1(int a,int q){
  int e, k, g;

  e=(a%28)+12;
  k=0;
  g=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (\at(a, Pre) % 28) + 12;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g >= 8;
  loop invariant e == \at(a, Pre) % 28 + 12;

  loop invariant e == (\at(a, Pre) % 28) + 12 && a == \at(a, Pre);
  loop invariant q == \at(q, Pre) && g >= 8;

  loop invariant a == \at(a, Pre) && q == \at(q, Pre) && g >= 8;
  loop invariant e == (\at(a,Pre) % 28) + 12 && a == \at(a,Pre) && q == \at(q,Pre);

  loop invariant e == (\at(a, Pre) % 28) + 12 && g >= 8;
  loop invariant a == \at(a, Pre) && q == \at(q, Pre);
  loop assigns g;
*/
while (1) {
      g = g+3;
      g = g*g+g;
  }

}
