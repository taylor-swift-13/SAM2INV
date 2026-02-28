int main1(int a,int n){
  int r, c, v;

  r=44;
  c=r;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 44;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= c;
  loop invariant c <= 44;
  loop invariant c >= 0;
  loop invariant (a >= 0) ==> (v >= 0);
  loop invariant (a <= 0) ==> (v <= 0);
  loop assigns v, c;
*/
while (c>=1) {
      v = v*2;
      c = c/2;
  }

}
