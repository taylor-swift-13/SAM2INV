int main1(int a,int p){
  int f, m, x;

  f=a+18;
  m=0;
  x=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 1 + (m*(m-1))/2;

  loop invariant f == \at(a, Pre) + 18;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant f == a + 18;
  loop invariant x == 1 + m*(m-1)/2;
  loop invariant m >= 0;
  loop invariant (m <= f) || (f < 0);
  loop invariant 0 <= m;


  loop assigns x, m;
*/
while (m<f) {
      x = x+m;
      m = m+1;
  }

}
