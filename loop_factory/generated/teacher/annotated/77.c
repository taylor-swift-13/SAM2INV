int main1(int a,int n){
  int y, i, c, v, p;

  y=40;
  i=0;
  c=a;
  v=a;
  p=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i && i <= y;
  loop invariant a == \at(a, Pre);
  loop invariant v == \at(a, Pre);
  loop invariant p == -8;
  loop invariant c == \at(a, Pre) + i*(v + p + 1);
  loop invariant n == \at(n, Pre);
  loop invariant c == a + i*(a - 7);
  loop invariant 0 <= i;
  loop invariant i <= y;
  loop assigns c, i;
*/
while (i<y) {
      c = c+v+p;
      c = c+1;
      i = i+1;
  }

}
