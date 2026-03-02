int main1(int a,int q){
  int c, u, b;

  c=a;
  u=0;
  b=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(a, Pre);
  loop invariant a == \at(a, Pre);

  loop invariant a == \at(a, Pre) && q == \at(q, Pre);
  loop invariant c == a && ((u == 0) ==> (b == 4));
  loop invariant (0 <= u) && ((u > 0) ==> (b <= a));
  loop invariant c == a;
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= u;
  loop invariant (b <= a) || (b == 4);
  loop invariant (u == 0) ==> (b == 4);
  loop invariant c == a && a == \at(a, Pre);
  loop invariant 0 <= u && c == a;

  loop invariant u >= 0;
  loop invariant c < 0 || u <= c;

  loop invariant c == a && a == \at(a, Pre) && q == \at(q, Pre);

  loop assigns b, u;
*/
while (u<=c-1) {
      b = b*b+b;
      b = a-b;
      u = u+1;
  }

}
