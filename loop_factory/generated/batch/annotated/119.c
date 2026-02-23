int main1(int a){
  int u, x, v;

  u=a;
  x=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 0 && (u >= 0) ==> (x <= u) && (u < 0) ==> (x == 0);
  loop invariant u == a;

  loop invariant a == \at(a, Pre);
  loop invariant x >= 0;
  loop invariant (a >= 0) ==> (x <= a);
  loop invariant u == \at(a, Pre);

  loop assigns x;
*/
while (x<=u-1) {
      x = x+1;
  }

}
