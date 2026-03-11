int main1(int m,int n){
  int e, y, i, k;

  e=(m%6)+15;
  y=0;
  i=-2;
  k=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (i == -2) || (i == 0);
  loop invariant 0 <= y && y <= e;
  loop invariant e == ((\at(m,Pre) % 6) + 15);
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant e == (m % 6) + 15;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (y == 0) ==> (i == -2) && (y > 0) ==> (i == 0);
  loop invariant y <= e;
  loop invariant 0 <= y && y <= e &&
                   ((i == -2) || (i == 0)) &&
                   e == (\at(m,Pre) % 6) + 15 &&
                   m == \at(m,Pre) &&
                   n == \at(n,Pre);
  loop invariant e == (\at(m, Pre) % 6) + 15;
  loop invariant i == -2 || i == 0;
  loop invariant ((i == -2) || (i == 0));
  loop invariant y >= 0;
  loop invariant (y == 0) ==> (i == -2);
  loop invariant i <= 0 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (y <= e) && ((y == 0) ==> (i == -2)) && ((y > 0) ==> (i == 0));
  loop invariant y <= e && 0 <= y && m == \at(m, Pre) && n == \at(n, Pre) && (y == 0 ==> i == -2) && (y > 0 ==> i == 0);
  loop assigns i, y;
*/
while (y<=e-1) {
      i = i*i+i;
      i = i%2;
      y = y+1;
  }

}
